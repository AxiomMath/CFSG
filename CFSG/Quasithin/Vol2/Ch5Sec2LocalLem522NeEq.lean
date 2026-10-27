module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeSteps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_eq_D42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
    ∀ (Lh : Subgroup G) (k : ℕ),
      IsHatComp (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂ Lh →
      L₂ < Lh →
      ((SuzukiModel (O2Q L₂) 2 k ∧ Is2F4 k (O2Q Lh)) ∨
        (LieModel (O2Q L₂) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Lh))) →
      (∃ U P : Subgroup (O2Q Lh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
        Group.IsSolvable ↥P) →
      False

@[expose] def Stmt5_2_2_eq_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
    ∀ Lh : Subgroup G,
      IsHatComp (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂ Lh →
      L₂ < Lh → LieModel (O2Q L₂) .PSL 2 2 2 → ¬ IsLieTypeChar2 (O2Q Lh) →
      ¬ IsRank2LieChar2 (O2Q Lh) →
      A314Statement
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B)
          (T ⊓ Subgroup.normalizer (L₂ : Set G)))
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂)
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) Lh) →
      p = 3

@[expose] def Stmt5_2_2_eq_cartan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → L₂ < oTwoUpper H → LieModel (O2Q L₂) .PSL 2 2 2 →
      IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧
        Lin2.IsHallTwoPrimeOf (B ⊓ L₂) (L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup G) : Set G))

section General

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_of_pow_three_of_card_three {P : Subgroup G} (hP : Nat.card P = 3) {b : G}
    (hb : b ∈ Subgroup.normalizer (P : Set G)) (hb3 : b ^ 3 = 1) {d : G} (hd : d ∈ P) :
    b * d * b⁻¹ = d := by
  by_cases hd1 : d = 1
  · rw [hd1]
    group
  have hord : orderOf d = 3 := by
    have h1 : orderOf d ∣ 3 := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥P)
      rwa [Subgroup.orderOf_mk, hP] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have hgen : ∀ y ∈ P, y = 1 ∨ y = d ∨ y = d ^ 2 := by
    intro y hy
    have htop : Subgroup.zpowers (⟨d, hd⟩ : ↥P) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, hP]
    have hz : (⟨y, hy⟩ : ↥P) ∈ Subgroup.zpowers (⟨d, hd⟩ : ↥P) := by
      rw [htop]
      trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hk' : d ^ k = y := by simpa using congrArg Subtype.val hk
    have hmod := zpow_mod_orderOf d k
    rw [hord] at hmod
    have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      omega
    rcases hk3 with h0 | h0 | h0
    · left
      rw [← hk', ← hmod, h0, zpow_zero]
    · right; left
      rw [← hk', ← hmod, h0, zpow_one]
    · right; right
      rw [← hk', ← hmod, h0]
      exact zpow_natCast d 2
  have hx : b * d * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hb d).mp hd
  rcases hgen _ hx with h1 | h1 | h1
  · exfalso
    apply hd1
    calc d = b⁻¹ * (b * d * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  · exact h1
  · exfalso
    have h2 : ∀ j : ℕ, b ^ j * d * (b ^ j)⁻¹ = d ^ (2 ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc b ^ (j + 1) * d * (b ^ (j + 1))⁻¹ = b * (b ^ j * d * (b ^ j)⁻¹) * b⁻¹ := by
              group
          _ = b * d ^ (2 ^ j) * b⁻¹ := by rw [ih]
          _ = (b * d * b⁻¹) ^ (2 ^ j) := by rw [conj_pow]
          _ = d ^ (2 ^ (j + 1)) := by rw [h1, ← pow_mul, pow_succ, mul_comm]
    have h3 := h2 3
    rw [hb3, one_mul, inv_one, mul_one] at h3
    have h7 : d ^ 7 * d = 1 * d := by
      rw [one_mul, ← pow_succ]
      exact h3.symm
    have h7' : d ^ 7 = 1 := mul_right_cancel h7
    have := orderOf_dvd_of_pow_eq_one h7'
    rw [hord] at this
    norm_num at this

theorem false_of_card_three_of_elemAbelian_nine (hQ : quasithinIsQTKECat G) {M B P : Subgroup G}
    (hM : IsTwoLocal M) (hB : IsElemAbelian 3 B) (hB9 : Nat.card ↥B = 9) (hP : Nat.card ↥P = 3)
    (hBM : B ≤ M) (hPM : P ≤ M) (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hPB : ¬ P ≤ B) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ b ∈ B, ∀ d ∈ P, b * d = d * b := fun b hb d hd => by
    have := conj_eq_of_pow_three_of_card_three hP (hBP hb) (hB.2 b hb) hd
    calc b * d = b * d * b⁻¹ * b := by group
      _ = d * b := by rw [this]
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    have : IsCyclic ↥P := isCyclic_of_prime_card (p := 3) hP
    intro x hx y hy
    have := (IsCyclic.commGroup (α := ↥P)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP3 : ∀ d ∈ P, d ^ 3 = 1 := fun d hd => by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨d, hd⟩)
    rw [hP] at this
    exact congrArg Subtype.val this
  have hPNB : P ≤ Subgroup.normalizer (B : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hcomm x hx d hd)
  have hEset := Subgroup.coe_mul_of_left_le_normalizer_right P B hPNB
  have hmemE : ∀ x ∈ P ⊔ B, ∃ d ∈ P, ∃ b ∈ B, d * b = x := by
    intro x hx
    have hx' : x ∈ ((P ⊔ B : Subgroup G) : Set G) := hx
    rw [hEset] at hx'
    obtain ⟨d, hd, b, hb, hdb⟩ := hx'
    exact ⟨d, hd, b, hb, hdb⟩
  have hEcomm : ∀ x ∈ P ⊔ B, ∀ y ∈ P ⊔ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨d, hd, b, hb, rfl⟩ := hmemE x hx
    obtain ⟨d', hd', b', hb', rfl⟩ := hmemE y hy
    calc d * b * (d' * b') = d * (b * d') * b' := by group
      _ = d * (d' * b) * b' := by rw [hcomm b hb d' hd']
      _ = (d * d') * (b * b') := by group
      _ = (d' * d) * (b' * b) := by rw [hPc d hd d' hd', hBc b hb b' hb']
      _ = d' * (d * b') * b := by group
      _ = d' * (b' * d) * b := by rw [hcomm b' hb' d hd]
      _ = d' * b' * (d * b) := by group
  have hE3 : ∀ x ∈ P ⊔ B, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨d, hd, b, hb, rfl⟩ := hmemE x hx
    rw [(Commute.mul_pow (hcomm b hb d hd).symm 3), hP3 d hd, hB.2 b hb, one_mul]
  have hEel : IsElemAbelian 3 (P ⊔ B) :=
    ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, hE3⟩
  have hE2 : IsPGroup 3 ↥(P ⊔ B) := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE2
  have h9 : 9 ∣ Nat.card ↥(P ⊔ B) := hB9 ▸ Subgroup.card_dvd_of_le le_sup_right
  have hne : Nat.card ↥(P ⊔ B) ≠ 9 := by
    intro h
    apply hPB
    have hBE : B = P ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, hB9])
    rw [hBE]
    exact le_sup_left
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    rw [hm] at h9 hne
    interval_cases m <;> simp_all
  have hrank : m ≤ CFSG.Open.pRank 3 M := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨P ⊔ B, sup_le hPM hBM, hEel, hm⟩
    rintro r ⟨E, -, -, hE⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num : 1 < 3)).le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E
  have h2 := pRank_le_two_of_isTwoLocal hQ Nat.prime_three (by norm_num) hM
  omega

end General

theorem stmt5_2_2_ne_eq_of (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hF : FactL2LieParabolic) (hLie : Stmt5_2_L2Lie) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h512 : Stmt5_1_12_loc)
    (hlie : Stmt5_1_13_loc_lie) (hD42 : Stmt5_2_2_eq_D42) (h3 : Stmt5_2_2_eq_three)
    (hcart : Stmt5_2_2_eq_cartan) : Stmt5_2_2_ne_eq := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hT₀N : T₀ ≤ Subgroup.normalizer (L₂ : Set G) := inf_le_right
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hT₀X : T₀ ≤ X₀ := le_sup_right.trans le_sup_left
  have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
  obtain ⟨hL₂c, k, hk, hbend⟩ : L₂ ∈ cComp L₂ ∧ ∃ k, 2 ≤ k ∧ IsBenderCh5 k (O2Q L₂) := by
    rcases hcase with ⟨⟨k, hk, hB⟩, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
    · exact ⟨cComp_mem_of_le hK₁ le_rfl (le_of_mem_cComp hK₁), k, hk, hB⟩
    · obtain ⟨k, hk, htype, -, hMK⟩ :=
        nonBender_type h510 hyp.toHyp5_1_8 hyp.notation59 hK₁ hnb hK1eq
      have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
        A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
      obtain ⟨-, hpsl, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
      exact ⟨cComp_mem_of_le hL₂P le_rfl (le_of_mem_cComp hL₂P), k, hk,
        Or.inl (Or.inl ⟨by decide, hpsl⟩)⟩
  have hL₂T₀ : L₂ ∈ lFamily T₀ := by
    refine cComp_mem_of_subnormal (IsSubnormal.step le_sup_left ?_ (IsSubnormal.refl _)) hL₂c
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT₀N)
  obtain ⟨Lh, ⟨hLh, hL₂Lh⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hOX hT₀syl hL₂X hL₂T₀
  have hhat : IsHatComp X₀ L₂ Lh := ⟨hLh, hL₂Lh, fun Y hY hL₂Y => huniq Y ⟨hY, hL₂Y⟩⟩
  have hT₀Lh : T₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    intro t ht
    have hKt : Lh.map (MulAut.conj t).toMonoidHom ∈ cComp X₀ := map_conj_mem_cComp hLh (hT₀X ht)
    have hL₂t : L₂ ≤ Lh.map (MulAut.conj t).toMonoidHom := by
      intro x hx
      have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ L₂ :=
        (Subgroup.mem_normalizer_iff.mp (hT₀N (T₀.inv_mem ht)) x).mp hx
      refine ⟨t⁻¹ * x * t, hL₂Lh (by simpa using hx'), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    exact A38.map_conj_eq_iff.mp (hhat.2.2 _ hKt hL₂t)
  have hXN : X₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hOX hT₀syl hLh
    rwa [Emb512.conjClosure_hat_eq hT₀Lh] at this
  have hlt : L₂ < Lh := lt_of_le_of_ne hL₂Lh fun heq => hDp (by
    rw [heq]
    exact hDpX.trans hXN)
  have hodd : ∀ m ∈ Dp, Odd (orderOf m) := by
    intro m hm
    have h1 : orderOf m ∣ p := by
      rw [← hyp.card_Dp]
      have := orderOf_dvd_natCard (⟨m, hm⟩ : ↥Dp)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (by rcases hyp.p_cases with rfl | rfl <;> decide) h1
  have case34 : ∀ k : ℕ, ((SuzukiModel (O2Q L₂) 2 k ∧ Is2F4 k (O2Q Lh)) ∨
      (LieModel (O2Q L₂) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Lh))) → False := by
    intro k htype
    by_cases hres : ∃ U P : Subgroup (O2Q Lh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
        Group.IsSolvable ↥P
    · exact hD42 G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl Lh k hhat hlt
        htype hres
    ·
      have hD := hyp.notation59.2.1
      have hDcyc := (h.isCyclic_card_of_isHall l2TorusFact hD).1
      have hDs : Group.IsSolvable ↥D := by
        have := hDcyc
        exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
      have hTLs : Group.IsSolvable ↥(T ⊓ L) := by
        have := (h.sylow.1.to_le (inf_le_left : T ⊓ L ≤ T)).isNilpotent
        infer_instance
      have hBs : Group.IsSolvable ↥(borelL T L) := by
        rw [← h.borelL_eq_sup hD, sup_comm]
        exact A3.isSolvable_sup_of_le_normalizer (hD.1.trans inf_le_right)
      have hBTs : Group.IsSolvable ↥(borelL T L ⊔ T) := by
        have : Group.IsSolvable ↥T := by
          have := h.sylow.1.isNilpotent
          infer_instance
        exact A3.isSolvable_sup_of_le_normalizer h.T_le_normalizer_borel
      have hAs : Group.IsSolvable ↥((borelL T L ⊔ T) ⊓ X₀) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (inf_le_left : (borelL T L ⊔ T) ⊓ X₀ ≤ _))
          (Subgroup.inclusion_injective _)
      have hT₀A : T₀ ≤ (borelL T L ⊔ T) ⊓ X₀ := le_inf (inf_le_left.trans le_sup_right) hT₀X
      have hDpA : Dp ≤ (borelL T L ⊔ T) ⊓ X₀ :=
        le_inf ((hyp.Dp_le.trans hD.1).trans le_sup_left) hDpX
      apply hDp
      intro m hm
      exact hlie G h.simple h.nonabelian h.qtke T₀ X₀ L₂ Lh ((borelL T L ⊔ T) ⊓ X₀) k hOX
        hT₀syl hL₂X hL₂T₀ hT₀N hhat hlt htype hres hT₀A inf_le_right hAs m (hDpA hm)
        (hodd m hm)
  rcases h512 G h.simple h.nonabelian h.qtke T₀ X₀ L₂ Lh k hk hOX hT₀syl hL₂X hL₂T₀ hT₀N hhat hlt
      hbend with h3' | h4' | ⟨hL4, hnl, h314⟩
  · exact case34 k (Or.inl h3')
  · exact case34 k (Or.inr h4')
  ·
    by_cases hR2 : IsRank2LieChar2 (O2Q Lh)
    · exact case34 2 (Or.inr ⟨hL4, hR2⟩)
    have hp3 : p = 3 :=
      h3 G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl Lh hhat hlt hL4 hnl hR2
        h314
    obtain ⟨hBel, hB9, -⟩ := hcart G T M L V H B D L₂ Dp n p hyp hL₂K hL4
    have hD := hyp.notation59.2.1
    have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
    have hDp3 : Nat.card ↥Dp = 3 := hyp.card_Dp.trans hp3
    have hBDp : B ≤ Subgroup.normalizer (Dp : Set G) := fun b hb =>
      mem_normalizer_of_le_of_isCyclic hDcyc hyp.Dp_le (hyp.notation59.2.2 hb)
    have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
    have hDpM : Dp ≤ M :=
      (hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_left)).trans h.L_le
    have hBN := hyp.B_le_normalizer_L2 h510 h331 hR hLie
    exact false_of_card_three_of_elemAbelian_nine h.qtke h.maxTwoLocal.1 hBel hB9 hDp3 hBM hDpM
      hBDp fun hle => hDp (hle.trans hBN)

end CFSG.Quasithin.H13
