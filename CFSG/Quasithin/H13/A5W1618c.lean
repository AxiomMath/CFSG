module

public import CFSG.Quasithin.H13.A5W1618b
public import CFSG.Quasithin.Background.FFC4G2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

local notation "StSL" => Assembly.LowTwoRank.StatedSL

theorem exists_orderOf_four_alt6 : ∃ x : ↥(alternatingGroup (Fin 6)), orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5
  have hσ : σ ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  refine ⟨⟨σ, hσ⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  have h1 : ¬ σ ^ 2 ^ 1 = 1 := by decide
  have h2 : σ ^ 2 ^ (1 + 1) = 1 := by decide
  exact orderOf_eq_prime_pow h1 h2

theorem card_sl2_lt {k n : ℕ} (h : k < n) : 2 ^ k * (4 ^ k - 1) < 2 ^ n * (4 ^ n - 1) := by
  have h1 : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h
  have h2 : 4 ^ k < 4 ^ n := Nat.pow_lt_pow_right (by norm_num) h
  have h3 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h4 : 4 ^ k - 1 < 4 ^ n - 1 := by omega
  calc 2 ^ k * (4 ^ k - 1) ≤ 2 ^ n * (4 ^ k - 1) := Nat.mul_le_mul_right _ h1.le
    _ < 2 ^ n * (4 ^ n - 1) := Nat.mul_lt_mul_of_pos_left h4 (by positivity)

theorem eq_of_card_sl2 {k n : ℕ} (h : 2 ^ k * (4 ^ k - 1) = 2 ^ n * (4 ^ n - 1)) : k = n := by
  rcases Nat.lt_trichotomy k n with hlt | heq | hgt
  · exact absurd h (card_sl2_lt hlt).ne
  · exact heq
  · exact absurd h (card_sl2_lt hgt).ne'

theorem card_sl2_gt {n : ℕ} (hn : 3 ≤ n) : 120 < 2 ^ n * (4 ^ n - 1) := by
  calc 120 < 2 ^ 3 * (4 ^ 3 - 1) := by norm_num
    _ ≤ 2 ^ n * (4 ^ n - 1) := by
      rcases Nat.eq_or_lt_of_le hn with h3 | h3
      · rw [← h3]
      · exact (card_sl2_lt h3).le

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem piece_natural_real {G₁ : Subgroup (MulAut V)} {W C : Subgroup V} {F : Type} [Field F]
    [CharP F 2] (e : ↥G₁ ≃* ↥(StSL 2 F)) (hp : B56Piece G₁ W C) :
    W = commV G₁ ⊔ C ∧ ∃ (k : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StSL 2 K) →* ↥G₁),
      Nat.card K = 2 ^ k ∧ (FFModel.nat (StSL 2 K)).RealizesVia G₁ W C π := by
  rcases hp with ⟨hW, ⟨k, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩⟩ |
    ⟨-, m, K, _, _, hK, I, π, -, -, -, hreal⟩ | ⟨⟨e₃⟩, -⟩
  · exact ⟨hW, k, K, inferInstance, inferInstance, π, hK, hπ⟩
  · exact (false_of_injective_four e (FFC.injective_of_faithful_sec (FFC.symDn_faithful le_rfl) hπ)
      orderOf_cycle4).elim
  · have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact (false_of_injective_four e
      (FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ) hγ).elim
  · have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact (false_of_injective_four e
      (FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)) hγ).elim
  · obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := ZMod 2)
    exact (false_of_injective_four e (π := e₃.symm.toMonoidHom) e₃.symm.injective hγ).elim

theorem mem_of_pow_three {Γ : Type} [Group Γ] [Finite Γ] {J L T : Subgroup Γ} (hLJ : L ≤ J)
    (hLn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hT : IsPGroup 2 T) (hJ : J = L ⊔ T) {x : Γ}
    (hx : x ∈ J) (hx3 : x ^ 3 = 1) : x ∈ L := by
  have hn : (L.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff hLJ).2 fun h k hh hk => hLn k hk h hh
  have hTJ : T ≤ J := hJ ▸ le_sup_right
  have hidx : ∃ k : ℕ, (L.subgroupOf J).index = 2 ^ k := by
    have hTN : T ≤ Subgroup.normalizer (L : Set Γ) := fun t ht =>
      B6.mem_normalizer_of_forall_mem (fun l hl => hLn t (hTJ ht) l hl) fun l hl => by
        have := hLn t⁻¹ (J.inv_mem (hTJ ht)) l hl
        rwa [inv_inv] at this
    have h1 : L.relIndex (L ⊔ T) = (L ⊓ T).relIndex T := by
      rw [sup_comm, inf_comm]
      exact (A4.relIndex_sup_eq_of_le_normalizer' hTN).trans (Subgroup.inf_relIndex_left T L).symm
    have h2 : (L ⊓ T).relIndex T ∣ Nat.card ↥T :=
      Subgroup.index_dvd_card ((L ⊓ T).subgroupOf T)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT
    rw [hm] at h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    refine ⟨k, ?_⟩
    show L.relIndex J = 2 ^ k
    rw [hJ, h1, hk]
  obtain ⟨k, hk⟩ := hidx
  have hpow : x ^ 2 ^ k ∈ L := by
    have := Subgroup.pow_index_mem (L.subgroupOf J) (⟨x, hx⟩ : ↥J)
    rw [hk, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) 3 :=
    Nat.Coprime.pow_left _ (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 ^ k * a) % 3 = 1 := by
    refine ⟨(2 ^ k) ^ (Nat.totient 3 - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.mpr (by norm_num))]
    exact Nat.ModEq.pow_totient hcop
  have e2 : x = (x ^ 2 ^ k) ^ a := by
    rw [← pow_mul, ← Nat.mod_add_div (2 ^ k * a) 3, ha, pow_add, pow_mul, hx3, one_pow,
      mul_one, pow_one]
  rw [e2]
  exact L.pow_mem hpow a

theorem not_threeRank2_of_sup {Γ : Type} [Group Γ] [Finite Γ] {J L T : Subgroup Γ}
    (hLJ : L ≤ J) (hLn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hT : IsPGroup 2 T)
    (hJ : J = L ⊔ T) (hL : ¬ FFC.ThreeRank2 ↥L) : ¬ FFC.ThreeRank2 ↥J := by
  rintro ⟨x, y, hx1, hx3, hy3, hxy, hy⟩
  have hxL : (x : Γ) ∈ L := mem_of_pow_three hLJ hLn hT hJ x.2 (by
    have := congrArg Subtype.val hx3
    simpa using this)
  have hyL : (y : Γ) ∈ L := mem_of_pow_three hLJ hLn hT hJ y.2 (by
    have := congrArg Subtype.val hy3
    simpa using this)
  refine hL ⟨⟨x, hxL⟩, ⟨y, hyL⟩, fun h => hx1 (Subtype.ext (by simpa using congrArg Subtype.val h)),
    Subtype.ext (by simpa using congrArg Subtype.val hx3),
    Subtype.ext (by simpa using congrArg Subtype.val hy3),
    Subtype.ext (by simpa using congrArg Subtype.val hxy), fun hmem => hy ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simpa using this

theorem eq_factor_of_sl2 {G N : Subgroup (MulAut V)} (hf : B56FactorList ↥G) (hNG : N ≤ G)
    (hNn : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥N ≃* ↥(StSL 2 F)) : N = G := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have hcardN : Nat.card ↥N = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
  have hle : Nat.card ↥N ≤ Nat.card ↥G := Subgroup.card_le_of_le hNG
  rcases hf with ⟨k, K, _, _, hk1, hK, ⟨eG⟩⟩ | ⟨⟨eG⟩⟩ | ⟨m, K, _, _, hm1, hmodd, hK, ⟨eG⟩⟩
  · have hcharK : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    rcases Nat.lt_or_ge k 2 with hk | hk
    · exfalso
      have hk1' : k = 1 := by omega
      subst hk1'
      have hG : Nat.card ↥G = 6 := by
        rw [Nat.card_congr eG.toEquiv, R3c.card_statedSL_two_pow hK]
        norm_num
      have := card_sl2_gt hn
      omega
    · have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      exact eq_of_normal_simple hNG hNn hq
        (@MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) eG)
  · exfalso
    have hG : Nat.card ↥G = 120 := by
      rw [Nat.card_congr eG.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := card_sl2_gt hn
    omega
  · exfalso
    have hcharK : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    have hs := @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_three_odd hK hmodd)
      eG
    have hNG' := eq_of_normal_simple hNG hNn hq hs
    subst hNG'
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact orderOf_ne_four_of_equiv e (eG.symm γ) (by rw [MulEquiv.orderOf_eq]; exact hγ)

theorem sl2_natural_of_b56
    (hV : ∀ v : V, v ^ 2 = 1) {J N : Subgroup (MulAut V)} (hb : B53Hyp J)
    (h : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) (hNJ : N ≤ J)
    (hNn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥N ≃* ↥(StSL 2 F)) :
    ∃ (G₂ : Subgroup (MulAut V)) (U C : Subgroup V) (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(StSL 2 K) →* ↥N), Nat.card K = 2 ^ n ∧ N ⊔ G₂ = J ∧ N ⊓ G₂ = ⊥ ∧
      (∀ a ∈ N, ∀ b ∈ G₂, a * b = b * a) ∧ (FFModel.nat (StSL 2 K)).RealizesVia N U C π ∧
      (∀ g ∈ N, ∀ c ∈ C, g c = c) ∧ (∀ g ∈ N, ∀ v : V, g v * v⁻¹ ∈ U) := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have hcardN : Nat.card ↥N = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
  have hKcard : ∀ {k : ℕ} {K : Type} [Field K] [Finite K] {U C : Subgroup V}
      {π : ↥(StSL 2 K) →* ↥N}, Nat.card K = 2 ^ k →
      (FFModel.nat (StSL 2 K)).RealizesVia N U C π → Nat.card K = 2 ^ n := by
    intro k K _ _ U C π hK hπ
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hbij : Nat.card ↥(StSL 2 K) = Nat.card ↥N := Nat.card_eq_of_bijective π ⟨hinj, hπ.1⟩
    rw [R3c.card_statedSL_two_pow hK, hcardN] at hbij
    rw [hK, eq_of_card_sl2 hbij]
  have hcomm : ∀ {G : Subgroup (MulAut V)}, ∀ g ∈ G, ∀ v : V, g v * v⁻¹ ∈ commV G :=
    fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  have hfixJ : ∀ g ∈ N, ∀ c ∈ fixV J, g c = c := fun g hg c hc => hc g (hNJ hg)
  rcases h with hc1 | hc2 | hc3 | hc4 | hc5
  ·
    obtain ⟨hqF, hB51, hlist⟩ := hc1
    set L := quasithinGenFitting J with hL
    have hFJ : L ≤ J := quasithinGenFitting_le J
    have hFsub : IsSubnormal L J :=
      IsSubnormal.step hFJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hFJ).2
        (le_normalizer_quasithinGenFitting J)) (IsSubnormal.refl J)
    have hNL : N = L := by
      rcases B113.component_le_or_commutator_eq_bot (isComponentOf_of_qs_normal hNJ hNn hq)
          hFsub with hNF | hNF
      · exact eq_of_normal_qs hNF (fun m hm n hn => hNn m (hFJ hm) n hn) hq hqF
      · exfalso
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hNF
        have hNF' : N ≤ quasithinGenFitting J :=
          (le_inf hNJ hNF).trans (centralizer_quasithinGenFitting_le J)
        exact not_le_centralizer_self_of_qs hq
          (hNF.trans (Subgroup.centralizer_le fun x hx => hNF' hx))
    obtain ⟨T, -, hTJ⟩ := exists_isSylowTwoOf_of_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ J)
      IsPGroup.of_bot
    have hJLT : J = L ⊔ T := by
      have hTL : ∀ h : J = L, J = L ⊔ T := fun h =>
        le_antisymm (h ▸ le_sup_left) (sup_le hFJ hTJ.1)
      obtain ⟨-, hcases⟩ := hB51.1
      rcases hcases with hi | hii | ⟨k, hiii⟩ | hiv
      · rcases hi.2.2 T hTJ with h1 | ⟨h1, -⟩
        · exact hTL h1
        · exact h1
      · exact hTL hii.1
      · exact hTL hiii.1
      · exact hTL hiv.1
    have hLn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
      rw [← hNL]
      exact hNn
    have hno : ¬ FFC.ThreeRank2 ↥J := by
      refine not_threeRank2_of_sup hFJ hLn hTJ.2.1 hJLT fun h3 => ?_
      rw [← hNL] at h3
      exact not_threeRank2_statedSL_two (h3.of_mulEquiv e)
    have hJne : J ≠ ⊥ := fun h0 => (qs_perfect_ne_bot hq).2 (le_bot_iff.mp (h0 ▸ hNJ))
    obtain ⟨hfl, hpc⟩ := FFC.good_of_case1 FFC.b58Inputs V hV J hb hJne hno ⟨hqF, hB51, hlist⟩
    have hNJeq : N = J := eq_factor_of_sl2 hfl hNJ hNn hq hn hF e
    subst hNJeq
    obtain ⟨-, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hpc
    refine ⟨⊥, ⊤, fixV N, K, inferInstance, inferInstance, π, hKcard hK hπ, sup_bot_eq N,
      inf_bot_eq N, fun a _ b hb => by rw [Subgroup.mem_bot.mp hb, mul_one, one_mul], hπ,
      hfixJ, fun g _ v => Subgroup.mem_top _⟩
  ·
    exfalso
    obtain ⟨⟨eJ⟩, -, -⟩ := hc2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact not_qs_of_le_solvable hNJ
      (Group.isSolvable_of_isSolvable_injective (f := eJ.toMonoidHom) eJ.injective) hq
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, -, -, -, -, -, -, hp₁, hp₂⟩ := hc3
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_qs_normal hsup hc hNJ hNn hq with h1 | h1
    · have hNe := eq_factor_of_sl2 hf₁ h1 (fun x hx n hn => hNn x (hG₁J hx) n hn) hq hn hF e
      subst hNe
      obtain ⟨hW, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hp₁
      refine ⟨G₂, W₁, fixV J, K, inferInstance, inferInstance, π, hKcard hK hπ, hsup, hinf, hc,
        hπ, hfixJ, fun g hg v => ?_⟩
      rw [hW]
      exact Subgroup.mem_sup_left (hcomm g hg v)
    · have hNe := eq_factor_of_sl2 hf₂ h1 (fun x hx n hn => hNn x (hG₂J hx) n hn) hq hn hF e
      subst hNe
      obtain ⟨hW, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hp₂
      refine ⟨G₁, W₂, fixV J, K, inferInstance, inferInstance, π, hKcard hK hπ,
        by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
        fun a ha b hb => (hc b hb a ha).symm, hπ, hfixJ, fun g hg v => ?_⟩
      rw [hW]
      exact Subgroup.mem_sup_left (hcomm g hg v)
  ·
    exfalso
    obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, h3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := hc4
    have hMJ : G₁ ⊔ G₂ ≤ J := hJt ▸ le_sup_left
    have hG₁J : G₁ ≤ J := le_sup_left.trans hMJ
    obtain ⟨hp, -⟩ := qs_perfect_ne_bot hq
    have hNM : N ≤ G₁ ⊔ G₂ := by
      rw [← hp]
      exact (Subgroup.commutator_mono hNJ hNJ).trans
        (commutator_le_of_zpowers hJt (mem_normalizer_sup ht₁ ht₂))
    rcases le_or_le_of_qs_normal rfl hc hNM (fun x hx n hn => hNn x (hMJ hx) n hn) hq with
      h1 | h1
    · have hs : IsSimpleGroup ↥G₁ :=
        @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e₁
      have hNe : N = G₁ := eq_of_normal_simple h1 (fun m hm n hn => hNn m (hG₁J hm) n hn) hq hs
      subst hNe
      obtain ⟨x, hx⟩ := exists_orderOf_four_alt6
      exact orderOf_ne_four_of_equiv e (e₁.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
      exact not_qs_of_le_solvable h1 inferInstance hq
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, hG₂⟩ := hc5
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hL3 : ∀ {Gi : Subgroup (MulAut V)}, (↥Gi ≃* ↥(StSL 3 (ZMod 2))) → Gi ≤ J → N ≤ Gi →
        False := fun {Gi} eGi hGJ hNG => by
      have hs : IsSimpleGroup ↥Gi :=
        @MulEquiv.isSimpleGroup _ _ _ _
          (NQRigid.isSimpleGroup_statedSL_three_odd (F := ZMod 2) (m := 1)
            (by rw [Nat.card_zmod]; norm_num) (by decide)) eGi
      have hNe : N = Gi := eq_of_normal_simple hNG (fun m hm n hn => hNn m (hGJ hm) n hn) hq hs
      subst hNe
      obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := ZMod 2)
      exact orderOf_ne_four_of_equiv e (eGi.symm γ) (by rw [MulEquiv.orderOf_eq]; exact hγ)
    rcases le_or_le_of_qs_normal hsup hc hNJ hNn hq with h1 | h1
    · exact (hL3 e₁ hG₁J h1).elim
    · rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨k, K, _, _, hK, π, hπ⟩
      · exact (hL3 e₂ hG₂J h1).elim
      · have hcharK : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
        have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
        let e₂ := MulEquiv.ofBijective π ⟨hi, hπ.1⟩
        have hle : Nat.card ↥N ≤ Nat.card ↥G₂ := Subgroup.card_le_of_le h1
        have hG₂card : Nat.card ↥G₂ = 2 ^ k * (4 ^ k - 1) := by
          rw [← Nat.card_congr e₂.toEquiv]
          exact R3c.card_statedSL_two_pow hK
        have hk : 2 ≤ k := by
          by_contra hk
          have : 2 ^ k * (4 ^ k - 1) ≤ 2 ^ 1 * (4 ^ 1 - 1) := by
            rcases Nat.lt_or_ge k 1 with h0 | h0
            · have : k = 0 := by omega
              subst this
              norm_num
            · have : k = 1 := by omega
              subst this
              exact le_rfl
          have := card_sl2_gt hn
          omega
        have h4 : 4 ≤ Nat.card K := by
          rw [hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        have hs : IsSimpleGroup ↥G₂ :=
          @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4)
            e₂.symm
        have hNe : N = G₂ := eq_of_normal_simple h1 (fun m hm n hn => hNn m (hG₂J hm) n hn) hq hs
        subst hNe
        refine ⟨G₁, commV N, fixV N ⊓ commV N, K, inferInstance, inferInstance, π,
          hKcard hK hπ, by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
          fun a ha b hb => (hc b hb a ha).symm, hπ, fun g hg c hc' => hc'.1 g hg,
          fun g hg v => hcomm g hg v⟩

end CFSG.Quasithin.H13.A5
