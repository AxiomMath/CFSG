module

public import CFSG.Quasithin.H13.A5W1618c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

local notation "StSL" => Assembly.LowTwoRank.StatedSL

theorem not_isPerfect_perm_five : ¬ Group.IsPerfect (Equiv.Perm (Fin 5)) := by
  intro h
  have hle : commutator (Equiv.Perm (Fin 5)) ≤ (Equiv.Perm.sign).ker :=
    Abelianization.commutator_subset_ker _
  have hs : Equiv.swap (0 : Fin 5) 1 ∈ (Equiv.Perm.sign).ker := by
    apply hle
    rw [Group.isPerfect_def.mp h]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, Equiv.Perm.sign_swap (by decide)] at hs
  exact absurd hs (by decide)

theorem false_of_statedSL_three_perm_five {K : Type} [Field K] {X : Type} [Group X]
    (e₃ : ↥(StSL 3 K) ≃* X) (θ : X ≃* Equiv.Perm (Fin 5)) : False := by
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (le_refl 3)
  have h1 : Group.IsPerfect ↥(StSL 3 K) :=
    Group.IsPerfect.ofSurjective (G := Matrix.SpecialLinearGroup (Fin 3) K)
      (f := (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
      (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).surjective
  exact not_isPerfect_perm_five (Group.IsPerfect.ofSurjective (G := ↥(StSL 3 K))
    (f := (e₃.trans θ).toMonoidHom) (e₃.trans θ).surjective)

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem symmetricNatural_of_piece {G₁ : Subgroup (MulAut V)} {W C : Subgroup V}
    (θ : ↥G₁ ≃* Equiv.Perm (Fin 5)) (hp : B56Piece G₁ W C) :
    W = commV G₁ ⊔ C ∧ SymmetricNatural G₁ W C 5 := by
  have h120 : Nat.card ↥G₁ = 120 := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rcases hp with ⟨hW, ⟨n, K, _, _, hK, π, hπ⟩ | hsym | ⟨m, K, _, _, hK, π, hπ⟩⟩ |
    ⟨-, m, K, _, _, hK, I, π, -, -, -, hreal⟩ | ⟨⟨e₃⟩, -⟩
  · exfalso
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hc : Nat.card ↥(StSL 2 K) = Nat.card ↥G₁ := Nat.card_eq_of_bijective π ⟨hinj, hπ.1⟩
    have h2 := R3c.card_statedSL_two_pow hK
    rw [hc, h120] at h2
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n <;> norm_num at h2
    · have := card_sl2_gt h3
      omega
  · exact ⟨hW, hsym⟩
  · have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    exact (false_of_statedSL_three_perm_five (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) θ).elim
  · have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)
    exact (false_of_statedSL_three_perm_five (MulEquiv.ofBijective π ⟨hinj, (hreal 0).1⟩)
      θ).elim
  · exact (false_of_statedSL_three_perm_five e₃.symm θ).elim

theorem eq_factor_or_perm_of_sl2_four {G N : Subgroup (MulAut V)} (hf : B56FactorList ↥G)
    (hNG : N ≤ G) (hNn : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N)
    {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4) (e : ↥N ≃* ↥(StSL 2 F)) :
    N = G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5)) := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  have hcardN : Nat.card ↥N = 60 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
    norm_num
  have hle : Nat.card ↥N ≤ Nat.card ↥G := Subgroup.card_le_of_le hNG
  rcases hf with ⟨k, K, _, _, hk1, hK, ⟨eG⟩⟩ | ⟨⟨eG⟩⟩ | ⟨m, K, _, _, hm1, hmodd, hK, ⟨eG⟩⟩
  · left
    have hcharK : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    rcases Nat.lt_or_ge k 2 with hk | hk
    · exfalso
      have hk1' : k = 1 := by omega
      subst hk1'
      have hG : Nat.card ↥G = 6 := by
        rw [Nat.card_congr eG.toEquiv, R3c.card_statedSL_two_pow hK]
        norm_num
      omega
    · have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      exact eq_of_normal_simple hNG hNn hq
        (@MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) eG)
  · exact Or.inr ⟨eG⟩
  · exfalso
    have hcharK : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    have hs := @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_three_odd hK hmodd)
      eG
    have hNG' := eq_of_normal_simple hNG hNn hq hs
    subst hNG'
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact orderOf_ne_four_of_equiv e (eG.symm γ) (by rw [MulEquiv.orderOf_eq]; exact hγ)

theorem sl2_four_of_b56
    (hV : ∀ v : V, v ^ 2 = 1) {J N : Subgroup (MulAut V)} (hb : B53Hyp J)
    (h : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) (hNJ : N ≤ J)
    (hNn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) {F : Type}
    [Field F] [Finite F] (hF4 : Nat.card F = 4) (e : ↥N ≃* ↥(StSL 2 F)) :
    (∃ (G₂ : Subgroup (MulAut V)) (U C : Subgroup V) (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(StSL 2 K) →* ↥N), Nat.card K = 4 ∧ N ⊔ G₂ = J ∧ N ⊓ G₂ = ⊥ ∧
      (∀ a ∈ N, ∀ b ∈ G₂, a * b = b * a) ∧ (FFModel.nat (StSL 2 K)).RealizesVia N U C π ∧
      (∀ g ∈ N, ∀ c ∈ C, g c = c) ∧ (∀ g ∈ N, ∀ v : V, g v * v⁻¹ ∈ U)) ∨
    (∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V), N ≤ G₁ ∧ G₁ ⊔ G₂ = J ∧
      G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
      Nonempty (↥G₁ ≃* Equiv.Perm (Fin 5)) ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV J ∧
      XMod.IsInv ↥J W₁ ∧ XMod.IsInv ↥J W₂ ∧ W₁ = commV G₁ ⊔ fixV J ∧
      SymmetricNatural G₁ W₁ (fixV J) 5) := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  have hcardN : Nat.card ↥N = 2 ^ 2 * (4 ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
  have hcardN60 : Nat.card ↥N = 60 := by rw [hcardN]; norm_num
  have hKcard : ∀ {k : ℕ} {K : Type} [Field K] [Finite K] {U C : Subgroup V}
      {π : ↥(StSL 2 K) →* ↥N}, Nat.card K = 2 ^ k →
      (FFModel.nat (StSL 2 K)).RealizesVia N U C π → Nat.card K = 4 := by
    intro k K _ _ U C π hK hπ
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hbij : Nat.card ↥(StSL 2 K) = Nat.card ↥N := Nat.card_eq_of_bijective π ⟨hinj, hπ.1⟩
    rw [R3c.card_statedSL_two_pow hK, hcardN] at hbij
    rw [hK, eq_of_card_sl2 hbij]
    norm_num
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
    rcases eq_factor_or_perm_of_sl2_four hfl hNJ hNn hq hF4 e with hNJeq | hθ
    · left
      subst hNJeq
      obtain ⟨-, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hpc
      exact ⟨⊥, ⊤, fixV N, K, inferInstance, inferInstance, π, hKcard hK hπ, sup_bot_eq N,
        inf_bot_eq N, fun a _ b hb => by rw [Subgroup.mem_bot.mp hb, mul_one, one_mul], hπ,
        hfixJ, fun g _ v => Subgroup.mem_top _⟩
    · right
      obtain ⟨θ⟩ := hθ
      obtain ⟨hW, hsym⟩ := symmetricNatural_of_piece θ hpc
      refine ⟨J, ⊥, ⊤, fixV J, hNJ, sup_bot_eq J, inf_bot_eq J,
        fun a _ b hb => by rw [Subgroup.mem_bot.mp hb, mul_one, one_mul], ⟨θ⟩,
        top_sup_eq _, top_inf_eq _, fun _ _ _ => Subgroup.mem_top _, fun a w hw => ?_, hW,
        hsym⟩
      show (a : MulAut V) w ∈ fixV J
      rw [hw a a.2]
      exact hw
  ·
    exfalso
    obtain ⟨⟨eJ⟩, -, -⟩ := hc2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact not_qs_of_le_solvable hNJ
      (Group.isSolvable_of_isSolvable_injective (f := eJ.toMonoidHom) eJ.injective) hq
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, -, -, hinv₁, hinv₂, hW12, hWi, hp₁, hp₂⟩ :=
      hc3
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_qs_normal hsup hc hNJ hNn hq with h1 | h1
    · rcases eq_factor_or_perm_of_sl2_four hf₁ h1 (fun x hx n hn => hNn x (hG₁J hx) n hn) hq hF4
        e with hNe | hθ
      · left
        subst hNe
        obtain ⟨hW, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hp₁
        refine ⟨G₂, W₁, fixV J, K, inferInstance, inferInstance, π, hKcard hK hπ, hsup, hinf,
          hc, hπ, hfixJ, fun g hg v => ?_⟩
        rw [hW]
        exact Subgroup.mem_sup_left (hcomm g hg v)
      · right
        obtain ⟨θ⟩ := hθ
        obtain ⟨hW, hsym⟩ := symmetricNatural_of_piece θ hp₁
        exact ⟨G₁, G₂, W₁, W₂, h1, hsup, hinf, hc, ⟨θ⟩, hW12, hWi, hinv₁, hinv₂, hW, hsym⟩
    · rcases eq_factor_or_perm_of_sl2_four hf₂ h1 (fun x hx n hn => hNn x (hG₂J hx) n hn) hq hF4
        e with hNe | hθ
      · left
        subst hNe
        obtain ⟨hW, k, K, _, _, π, hK, hπ⟩ := piece_natural_real e hp₂
        refine ⟨G₁, W₂, fixV J, K, inferInstance, inferInstance, π, hKcard hK hπ,
          by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
          fun a ha b hb => (hc b hb a ha).symm, hπ, hfixJ, fun g hg v => ?_⟩
        rw [hW]
        exact Subgroup.mem_sup_left (hcomm g hg v)
      · right
        obtain ⟨θ⟩ := hθ
        obtain ⟨hW, hsym⟩ := symmetricNatural_of_piece θ hp₂
        exact ⟨G₂, G₁, W₂, W₁, h1, by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
          fun a ha b hb => (hc b hb a ha).symm, ⟨θ⟩, by rw [sup_comm]; exact hW12,
          by rw [inf_comm]; exact hWi, hinv₂, hinv₁, hW, hsym⟩
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
    left
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
          have h6 : 2 ^ k * (4 ^ k - 1) ≤ 6 := by
            rcases Nat.lt_or_ge k 1 with h0 | h0
            · have : k = 0 := by omega
              subst this
              norm_num
            · have : k = 1 := by omega
              subst this
              norm_num
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
        exact ⟨G₁, commV N, fixV N ⊓ commV N, K, inferInstance, inferInstance, π,
          hKcard hK hπ, by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
          fun a ha b hb => (hc b hb a ha).symm, hπ, fun g hg c hc' => hc'.1 g hg,
          fun g hg v => hcomm g hg v⟩

end CFSG.Quasithin.H13.A5
