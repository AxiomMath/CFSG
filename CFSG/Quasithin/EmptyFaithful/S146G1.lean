module

public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Quasithin.EmptyFaithful.S146Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Bridge

variable {G : Type} [Group G]

omit [Group G] in
private theorem comap_pCore_congr (p : ℕ) {X : Type} [Group X] (N N' : Subgroup X) [N.Normal]
    [N'.Normal] (h : N = N') :
    (CFSG.pCore p (X ⧸ N)).comap (QuotientGroup.mk' N) =
      (CFSG.pCore p (X ⧸ N')).comap (QuotientGroup.mk' N') := by
  subst h
  rfl

theorem mem_oTwoPIn_of_mem_pCore {q : ℕ} {H : Subgroup G} {x : G} (hx : x ∈ H)
    (h : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hx⟩ : OTwoQuot H) ∈
      CFSG.pCore q (OTwoQuot H)) : x ∈ oTwoPIn q H := by
  unfold oTwoPIn preimageModTwoCore
  rw [comap_pCore_congr q (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (CFSG.pCore_eq_open ↥H 2)]
  exact ⟨⟨x, hx⟩, h, rfl⟩

end Bridge

section Cases

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_oTwoPIn_of_solvable {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : (X.subgroupOf H).Normal) (hsolv : Group.IsSolvable ↥X) (hX : ¬ X ≤ pCoreOf 2 H) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ x ∈ X, x ∈ oTwoPIn q H ∧ x ∉ pCoreOf 2 H := by
  classical
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set X' : Subgroup ↥H := X.subgroupOf H with hX'
  set Xb : Subgroup (OTwoQuot H) := X'.map π with hXb
  have hXbn : Xb.Normal := Subgroup.Normal.map hXn π hπs
  have hXbne : Xb ≠ ⊥ := by
    intro hbot
    apply hX
    intro x hx
    have h1 : π ⟨x, hXH hx⟩ ∈ Xb := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨x, hXH hx⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hX'solv : Group.IsSolvable ↥X' :=
    Group.isSolvable_of_surjective (f := ((Subgroup.subgroupOfEquivOfLe hXH).symm : ↥X ≃* ↥X').toMonoidHom)
      (MulEquiv.surjective _)
  have hXbsolv : Group.IsSolvable ↥Xb := by
    let f : ↥X' →* ↥Xb := (π.comp X'.subtype).codRestrict Xb
      (fun x => Subgroup.mem_map_of_mem π x.2)
    refine Group.isSolvable_of_surjective (f := f) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨N, hNn, hNle, hNbot, hNmin⟩ := CFSG.exists_minimal_normal_le Xb hXbn hXbne
  have : N.Normal := hNn
  have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (hNmin K hK hKN hKb)⟩
  have : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNle)
  obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have : Fact q.Prime := ⟨hq⟩
  have hqg : IsPGroup q ↥N := CFSG.IsElementaryAbelian.isPGroup q ↥N
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hle : N ≤ CFSG.pCore 2 (OTwoQuot H) :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hqg
    rw [pCore_two_quot_eq_bot H, le_bot_iff] at hle
    exact hNbot hle
  have hNp : N ≤ CFSG.pCore q (OTwoQuot H) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hqg
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
  obtain ⟨y, hy, hya⟩ := hNle a.2
  have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  have hy' : (⟨(y : G), y.2⟩ : ↥H) = y := rfl
  refine ⟨q, hq, hq2, (y : G), hyX, mem_oTwoPIn_of_mem_pCore y.2 ?_, ?_⟩
  · rw [hy']
    have : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) y : OTwoQuot H) = (a : OTwoQuot H) := hya
    rw [this]
    exact hNp a.2
  · intro hyQ
    obtain ⟨z, hz, hzy⟩ := hyQ
    have hzy' : z = y := Subtype.ext hzy
    apply ha
    apply Subtype.ext
    rw [← hya, ← hzy']
    exact (QuotientGroup.eq_one_iff z).mpr hz

theorem exists_cComp_le_of_not_solvable {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : (X.subgroupOf H).Normal) (hsolv : ¬ Group.IsSolvable ↥X) :
    ∃ K ∈ cComp H, K ≤ X := by
  classical
  have hne : perfectCore X ≠ ⊥ := fun h => hsolv ((isSolvable_iff_perfectCore_eq_bot X).mpr h)
  have hperf : perfectCore (perfectCore X) = perfectCore X :=
    (perfectCore_eq_self_iff _).mpr (perfectCore_perfect X)
  have hsub : IsSubnormal (perfectCore X) H :=
    A3.subnormal_perfectCore (A3.subnormal_of_normal hXH hXn)
  obtain ⟨K, ⟨hKX, hKne, hKperf, hKsub⟩, hmin⟩ :=
    (InvImage.wf (fun K : Subgroup G => Nat.card K) wellFounded_lt).has_min
      {K | K ≤ perfectCore X ∧ K ≠ ⊥ ∧ perfectCore K = K ∧ IsSubnormal K H}
      ⟨perfectCore X, le_rfl, hne, hperf, hsub⟩
  refine ⟨K, mem_cComp_iff_minimal.mpr ⟨⟨hKne, hKperf, hKsub⟩, ?_⟩, hKX.trans (perfectCore_le X)⟩
  rintro K' ⟨hK'ne, hK'perf, hK'sub⟩ hK'K
  have hcard : Nat.card K ≤ Nat.card K' := not_lt.mp (hmin K' ⟨hK'K.trans hKX, hK'ne, hK'perf, hK'sub⟩)
  exact (Subgroup.eq_of_le_of_card_ge hK'K hcard).ge

end Cases

section Four

variable {G : Type} [Group G] [Finite G]

theorem stage1461Four_of (h2 : Stage1461Two) (h3 : Stage1461Three) : Stage1461Four := by
  intro G _ _ T M S H hH X hX hXO hXH hXn
  have hTH : T ≤ H := hH.1.1
  have hHm : H ≤ mcOf T := S.le_mcOf hH
  have hXTH : X ⊔ T ≤ H := sup_le hXH hTH
  have hZT : quasithinOmegaOneCenter T ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) := S.hyp.sylow.1.to_le hZT
  refine ⟨⟨le_sup_right, fun hbot => ?_⟩, fun hXTM => ?_⟩
  ·
    have hnorm : X ⊔ T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      (hXTH.trans hHm).trans S.normalizer_Z.ge
    have hle : quasithinOmegaOneCenter T ≤ pCoreOf 2 (X ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans le_sup_right) hnorm hZ2
    rw [hbot, le_bot_iff] at hle
    have hcard := S.card_Z
    rw [hle, Subgroup.card_bot] at hcard
    omega
  · have hXM : X ≤ M := le_sup_left.trans hXTM
    by_cases hsolv : Group.IsSolvable ↥X
    ·
      have hXQ : ¬ X ≤ pCoreOf 2 H := by
        intro hXQ
        apply hX
        have hX2 : IsPGroup 2 ↥X := (pCoreOf_isPGroup 2 H).to_le hXQ
        rw [← hXO]
        refine eq_bot_iff.mpr ?_
        refine (Subgroup.closure_le _).mpr fun x hx => ?_
        obtain ⟨k, hk⟩ := hX2 ⟨x, hx.1⟩
        have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
        have hodd := hx.2
        rw [hj] at hodd
        have hj0 : j = 0 := by
          by_contra hj0
          exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
        rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
        rw [SetLike.mem_coe, Subgroup.mem_bot]
        exact hj
      obtain ⟨q, hq, hq2, x, hxX, hxq, hxQ⟩ :=
        exists_mem_oTwoPIn_of_solvable hXH hXn hsolv hXQ
      exact hxQ (by rw [← h2 G T M S H hH q hq hq2]; exact ⟨hxq, hXM hxX⟩)
    ·
      obtain ⟨K, hK, hKX⟩ := exists_cComp_le_of_not_solvable hXH hXn hsolv
      exact h3 G T M S H hH K hK (hKX.trans hXM)

end Four

end CFSG.Quasithin
