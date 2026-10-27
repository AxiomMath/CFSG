module

public import CFSG.Quasithin.EmptyFaithful.S153LKsA
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.EmptyFaithful.LRed3FourA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

namespace S153L

section Orders

private theorem ksb_ord_of_cq {L S : Type} [Group L] [Finite L]
    [Group S] (hK : KsCover L) (e : L ⧸ Subgroup.center L ≃* S) : KsOrd (Nat.card S) := by
  obtain ⟨N, hN, hcard⟩ := hK.card_data_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  rw [Nat.card_congr e.toEquiv] at h1
  have h2 : N * Nat.card (Subgroup.center L) = Nat.card S * Nat.card (Subgroup.center L) := by
    rw [← hcard, h1]
  rwa [Nat.eq_of_mul_eq_mul_right hpos h2] at hN

private theorem ksb_card_ge {L : Type} [Group L] [Finite L]
    (h : KsCover L) : 504 ≤ Nat.card L := by
  obtain ⟨N, hN, hcard⟩ := h.card_data_eq
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  rw [hcard]
  exact (ksOrd_ge hN).trans (Nat.le_mul_of_pos_right _ hpos)

private theorem ksb_ord_of_card_center {L : Type} [Group L] [Finite L]
    (hK : KsCover L) (hZ : Nat.card (Subgroup.center L) = 1) : KsOrd (Nat.card L) := by
  obtain ⟨N, hN, hcard⟩ := hK.card_data_eq
  rw [hZ, mul_one] at hcard
  rwa [hcard]

private theorem ksb_not_ord {N : ℕ}
    (hN : N = 60 ∨ N = 360 ∨ N = 2520 ∨ N = 6048 ∨ N = 20160 ∨ N = 443520 ∨ N = 9999360) :
    ¬ KsOrd N := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ksOrd_ne_fixed h
  have := ksOrd_ge h
  omega

private theorem ksb_ord_of_simple_surj {L Γ : Type} [Group L]
    [Finite L] [Group Γ] (hq : CFSG.IsQuasisimple L) (hK : KsCover L) (hΓ : IsSimpleGroup Γ)
    (π : Γ →* L) (hπ : Function.Surjective π) : KsOrd (Nat.card Γ) := by
  obtain ⟨e⟩ := lred3_cq_simple hq hΓ π hπ
  exact ksb_ord_of_cq hK e

private theorem ksb_ord_of_isHat {L Γ₀ S : Type} [Group L]
    [Finite L] [Group Γ₀] [Group S] (hq : CFSG.IsQuasisimple L) (hK : KsCover L)
    (hhat : IsHat Γ₀ S) (π : Γ₀ →* L) (hπ : Function.Surjective π) : KsOrd (Nat.card S) := by
  obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hq π hπ
  obtain ⟨f⟩ := hhat.2.2
  exact ksb_ord_of_cq hK (e.symm.trans f)

end Orders

section Bad

variable {L : Type} [Group L] [Finite L]

private theorem ksb_false_alt (hq : CFSG.IsQuasisimple L)
    (hK : KsCover L) {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (π : ↥(alternatingGroup (Fin m)) →* L) (hπ : Function.Surjective π) : False := by
  have h := ksb_ord_of_simple_surj hq hK (isSimpleGroup_alt (by omega)) π hπ
  rw [card_alt m (by omega)] at h
  rcases hm with rfl | rfl | rfl
  · exact ksb_not_ord (by decide) h
  · exact ksb_not_ord (by decide) h
  · exact ksb_not_ord (by decide) h

private theorem ksb_false_sl_zmod (hq : CFSG.IsQuasisimple L)
    (hK : KsCover L) {n : ℕ} (hn : n = 4 ∨ n = 5) (π : ↥(StatedSL n (ZMod 2)) →* L)
    (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup ↥(StatedSL n (ZMod 2)) := isSimpleGroup_statedSL_two (by omega)
  have h := ksb_ord_of_simple_surj hq hK hs π hπ
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rcases hn with rfl | rfl
  · rw [card_statedSL, card_SL_four_of_two h2] at h
    exact ksb_not_ord (by norm_num) h
  · rw [card_statedSL, card_SL_five_of_two h2] at h
    exact ksb_not_ord (by norm_num) h

private theorem ksb_false_sl2 (hq : CFSG.IsQuasisimple L)
    (hK : KsCover L) {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hcard : Nat.card K = 2 ^ (2 * m)) (π : ↥(StatedSL 2 K) →* L)
    (hπ : Function.Surjective π) : False := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have h := ksb_ord_of_simple_surj hq hK hs π hπ
  have h44 : (4 : ℕ) ^ (2 * m) = 2 ^ (4 * m) := by
    rw [pow_mul, pow_mul]
    norm_num
  rw [card_statedSL, card_SL_two_pow hcard, h44] at h
  exact ksOrd_ne_orth hm h

private theorem ksb_false_g2 (hK : KsCover L) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (e : ↥(CFSG.Open.quasithinG2 K) ≃* L) : False := by
  have hcp : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hcard
  have h4 : 2 < Nat.card K := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := K) h4
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 K) = ⊥ := by
    rw [Alt57Model.quasithinG2_eq_cayleyGroup]
    exact CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hZ1 : Nat.card (Subgroup.center L) = 1 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZ, Subgroup.card_bot]
  have h := ksb_ord_of_card_center hK hZ1
  rw [← Nat.card_congr e.toEquiv] at h
  have hc : Nat.card ↥(CFSG.Open.quasithinG2 K) =
      2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [Alt57Model.quasithinG2_eq_cayleyGroup, CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hcard,
      ← pow_mul, ← pow_mul, mul_comm n 6, mul_comm n 2]
  rw [hc] at h
  exact ksOrd_ne_g2 hn h

private theorem ksb_false_g2derived
    (hq : CFSG.IsQuasisimple L) (hK : KsCover L) {K : Type}
    [Field K] [Finite K] (hK2 : Nat.card K = 2)
    (π : ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ →* L)
    (hπ : Function.Surjective π) : False := by
  have hs := CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK2
  have h := ksb_ord_of_simple_surj hq hK hs π hπ
  rw [card_g2Two_commutator hK2] at h
  exact ksb_not_ord (by norm_num) h

private theorem ksb_equiv_g2derived
    {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (N : Subgroup ↥(CFSG.Open.quasithinG2 K)) [N.Normal]
    (e : Y ≃* ↥N) :
    Nonempty (Y ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) := by
  have hs : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK
  have hD : (commutator ↥(CFSG.Open.quasithinG2 K)).map (CFSG.Open.quasithinG2 K).subtype =
      ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eD : ↥(commutator ↥(CFSG.Open.quasithinG2 K)) ≃*
      ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    ((commutator ↥(CFSG.Open.quasithinG2 K)).equivMapOfInjective
      (CFSG.Open.quasithinG2 K).subtype (CFSG.Open.quasithinG2 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hD)
  have hDs : IsSimpleGroup ↥(commutator ↥(CFSG.Open.quasithinG2 K)) := eD.isSimpleGroup
  have hYp : Group.IsPerfect Y := hY.1
  have : Group.IsPerfect ↥N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hY1 : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    apply hy
    have h1 : ((e y : ↥(⊥ : Subgroup ↥(CFSG.Open.quasithinG2 K))) :
        ↥(CFSG.Open.quasithinG2 K)) = 1 := Subgroup.mem_bot.1 (e y).2
    exact e.injective (Subtype.ext (by rw [h1]; simp))
  have heq : N = commutator ↥(CFSG.Open.quasithinG2 K) := eq_commutator_of_isPerfect N hN0 hDs
  exact ⟨(e.trans (MulEquiv.subgroupCongr heq)).trans eD⟩

end Bad

section Cases

private def KsGood {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L ⊤ ⊥ 2 n') ∨ (∃ f, BinaryNaturalSz L ⊤ ⊥ f) ∨
    (∃ a, BinaryNaturalSU3 L ⊤ ⊥ a) ∨ (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L ⊤ ⊥ 3 n') ∨
    (∃ n', 2 ≤ n' ∧ BinaryNaturalSp4 L ⊤ ⊥ n')

variable {Wt : Type} [CommGroup Wt] [Finite Wt] {G L A : Subgroup (MulAut Wt)}

private theorem ksb_case1 (hK : KsCover ↥L) (c : B42Case1 G L A) :
    KsGood L := by
  obtain ⟨-, ⟨n, hn⟩, -, -⟩ := c
  by_cases h2 : 2 ≤ n
  · exact Or.inl ⟨n, h2, hn⟩
  · exfalso
    obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
    have hn1 : n = 1 := by
      have := TypeList.one_le_of_card_eq_pow hcard
      omega
    subst hn1
    have h6 : Nat.card ↥L = 2 ^ 1 * (4 ^ 1 - 1) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hcard]
    norm_num at h6
    have := ksb_card_ge hK
    omega

private theorem ksb_case2 (hK : KsCover ↥L) (c : B42Case2 G L) :
    KsGood L := by
  obtain ⟨-, ⟨n, hn⟩, -⟩ := c
  by_cases h2 : 2 ≤ n
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h2, hn⟩)))
  · exfalso
    obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
    have hn1 : n = 1 := by
      have := TypeList.one_le_of_card_eq_pow hcard
      omega
    subst hn1
    have h6 : Nat.card ↥L = 2 ^ (3 * 1) * ((2 ^ (3 * 1) - 1) * (2 ^ (2 * 1) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hcard]
    norm_num at h6
    have := ksb_card_ge hK
    omega

private theorem ksb_case3 (hq : CFSG.IsQuasisimple ↥L)
    (hLJ : L ≤ ffJ G) (hnorm : (L.subgroupOf (ffJ G)).Normal) (hK : KsCover ↥L)
    (c : B42Case3 G L) : KsGood L := by
  obtain ⟨⟨n, hn, hn2⟩, -⟩ := c
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hn
    have hn1 := TypeList.one_le_of_card_eq_pow hcard
    have h1 : n = 1 := by omega
    subst h1
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    let π : Equiv.Perm (Fin 6) →* ↥(ffJ G) :=
      e.toMonoidHom.comp (Alt57Model.spEquivPerm K hK2).symm.toMonoidHom
    have hπ : Function.Surjective π :=
      e.surjective.comp (Alt57Model.spEquivPerm K hK2).symm.surjective
    have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLJ).symm hq
    obtain ⟨f⟩ := TypeList.perm_perfect_normal_equiv (n := 6) (by norm_num) π hπ _ hnorm
      hq'.1.commutator_eq_top (TypeList.exists_noncomm_of_quasisimple hq')
    let e6 : alternatingGroup (Fin 6) ≃* ↥L := f.trans (Subgroup.subgroupOfEquivOfLe hLJ)
    exact ksb_false_alt hq hK (Or.inr (Or.inl rfl)) e6.toMonoidHom e6.surjective
  · have heq : ffJ G = L := hn2 hge
    rw [heq] at hn
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hge, hn⟩)))

private theorem ksb_case4
    (hq : CFSG.IsQuasisimple ↥L) (hLJ : L ≤ ffJ G)
    (hnorm : (L.subgroupOf (ffJ G)).Normal) (hK : KsCover ↥L) (c : B42Case4 G L A) : False := by
  obtain ⟨⟨n, hn, -, hn2⟩, -⟩ := c
  obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := TypeList.exists_equiv_of_g2Natural hn
  have hn1 := TypeList.one_le_of_card_eq_pow hcard
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have h1 : n = 1 := by omega
    subst h1
    have hK2 : Nat.card K = 2 := by simpa using hcard
    have hN : ((L.subgroupOf (ffJ G)).map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map hnorm e.symm.toMonoidHom e.symm.surjective
    let eN : ↥L ≃* ↥((L.subgroupOf (ffJ G)).map e.symm.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.trans (e.symm.subgroupMap (L.subgroupOf (ffJ G)))
    obtain ⟨e'⟩ := ksb_equiv_g2derived hq hK2 _ eN
    exact ksb_false_g2derived hq hK hK2 e'.symm.toMonoidHom e'.symm.surjective
  · have heq : ffJ G = L := hn2 hge
    exact ksb_false_g2 hK hge hcard (e.trans (MulEquiv.subgroupCongr heq))

private theorem ksb_case5 (hq : CFSG.IsQuasisimple ↥L)
    (hLJ : L ≤ ffJ G) (hnorm : (L.subgroupOf (ffJ G)).Normal) (hK : KsCover ↥L)
    (c : B42Case5 G A) : False := by
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := c
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> omega
  have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLJ).symm hq
  obtain ⟨f⟩ := TypeList.perm_perfect_normal_equiv hn5 π hπ.1 _ hnorm hq'.1.commutator_eq_top
    (TypeList.exists_noncomm_of_quasisimple hq')
  let e6 : alternatingGroup (Fin n) ≃* ↥L := f.trans (Subgroup.subgroupOfEquivOfLe hLJ)
  exact ksb_false_alt hq hK (by omega) e6.toMonoidHom e6.surjective

private theorem ksb_case6 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case6 G L A) : False := by
  obtain ⟨-, ⟨π, hπ⟩, -, -, -⟩ := c
  exact ksb_false_alt hq hK (Or.inr (Or.inl rfl)) π hπ.1

private theorem ksb_case7 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case7 G L A) : False := by
  obtain ⟨-, -, ⟨α, π, hπ⟩, -⟩ := c
  exact ksb_false_alt hq hK (Or.inr (Or.inr rfl)) π hπ.1

private theorem ksb_case8 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case8 G L A) : False := by
  obtain ⟨-, -, -, K, hKf, hKfin, Γ₀, -, -, hhat, -, π, hπ, -⟩ := c
  have h := ksb_ord_of_isHat hq hK hhat π hπ.1
  rw [card_alt 6 (by norm_num)] at h
  exact ksb_not_ord (by decide) h

private theorem ksb_case9 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case9 G L) : False := by
  obtain ⟨-, n, hn, hnat, -⟩ := c
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  exact ksb_false_sl_zmod hq hK hn π hπ.1

private theorem ksb_case10 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case10 G L A) : False := by
  obtain ⟨⟨π, hπ⟩, -⟩ := c
  exact ksb_false_sl_zmod hq hK (Or.inl rfl) π hπ.1

private theorem ksb_case11 (hq : CFSG.IsQuasisimple ↥L)
    (hK : KsCover ↥L) (c : B42Case11 G L A) : False := by
  obtain ⟨-, -, -, -, π, hπ, -⟩ := c
  exact ksb_false_sl_zmod hq hK (Or.inr rfl) π hπ.1

end Cases

section Inspection

variable {Wt : Type} [CommGroup Wt] [Finite Wt] {G L : Subgroup (MulAut Wt)}

private theorem ksb_table
    (hq : CFSG.IsQuasisimple ↥L) (hK : KsCover ↥L) (ht : AsB45Table G L)
    (hqq : qOf G ≤ ((2 : ℚ) : WithTop ℚ)) : KsGood L := by
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, hsu, -⟩ | ⟨f, hsz, -⟩ |
      ⟨m, -, -, hq2, -⟩ | ⟨⟨K, _, _, hKc, π, hR⟩, -⟩ | ⟨-, hq2⟩ |
      ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ | ⟨-, hq2⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨-, hq2⟩
  ·
    exact (ksb_false_alt hq hK (m := 7) (Or.inr (Or.inr rfl)) π hR.1).elim
  ·
    obtain ⟨K, _, _, _, hKc, π, hR⟩ := horth
    exact (ksb_false_sl2 hq hK hm hKc π hR.1).elim
  · exact Or.inr (Or.inr (Or.inl ⟨m, hsu⟩))
  · exact Or.inr (Or.inl ⟨f, hsz⟩)
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    exact (ksb_false_g2derived hq hK (by rw [hKc]; norm_num) π hR.1).elim
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    have h := ksb_ord_of_isHat hq hK hhat π hR.1
    have hc : Nat.card ↥CFSG.Open.quasithinM22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [hc] at h
    exact (ksb_not_ord (by norm_num) h).elim
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    obtain ⟨hs, hc⟩ := stab_props_m22 hxy
    have h := ksb_ord_of_simple_surj hq hK hs π hR.1
    rw [hc] at h
    exact (ksb_not_ord (by norm_num) h).elim
  · exact absurd hq2 (not_lt.2 hqq)

private theorem ksb_good
    (h42 : AsB42) (h45 : AsB45) (hsv : ∀ v : Wt, v ^ 2 = 1) (hb4 : B4Hyp G L)
    (hqhat : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) (hqs : qOf G ≤ ((2 : ℚ) : WithTop ℚ))
    (hK : KsCover ↥L) : KsGood L := by
  have hq : CFSG.IsQuasisimple ↥L := hb4.2.2.1
  rcases h45 _ hsv _ _ hb4 hqhat with ⟨-, ⟨A, hA'⟩, -⟩ | ⟨-, ht⟩ | h3
  · have hLJ : L ≤ ffJ G :=
      TypeList.le_ffJ_of_b4Hyp (KP := CFSG.SectionRank.IsKGroupCat) hsv hb4 hA'
    have hnorm : (L.subgroupOf (ffJ G)).Normal := ⟨fun l hl g => by
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      have h1 := CFSG.Quasithin.le_normalizer_quasithinGenFitting G (TypeList.ffJ_le_self G g.2)
      rw [← hb4.2.1] at h1
      exact (Subgroup.mem_normalizer_iff.1 h1 _).1 hl⟩
    rcases h42 _ hsv _ _ hb4 A hA' with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
    · exact ksb_case1 hK c1
    · exact ksb_case2 hK c2
    · exact ksb_case3 hq hLJ hnorm hK c3
    · exact (ksb_case4 hq hLJ hnorm hK c4).elim
    · exact (ksb_case5 hq hLJ hnorm hK c5).elim
    · exact (ksb_case6 hq hK c6).elim
    · exact (ksb_case7 hq hK c7).elim
    · exact (ksb_case8 hq hK c8).elim
    · exact (ksb_case9 hq hK c9).elim
    · exact (ksb_case10 hq hK c10).elim
    · exact (ksb_case11 hq hK c11).elim
  · exact ksb_table hq hK ht hqs
  · exact absurd h3.2.1 (not_lt.2 hqs)

end Inspection

section Main

theorem typesFour_natW_of_stab
    (hA21 : AsA21SQTKSection) (h42 : AsB42) (h45 : AsB45) {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (hT : T ≤ stabSub V) (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ))
    (hfaith : L ⊓ centSub V = ⊥) (hKs : KsCover ↥L) : TypesFourShapeNatWSec L V := by
  subst hMp
  have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
  have hqhat := lred3_qhatOf_autSec hD rfl hT
  have hqs := lred3_qOf_autSec hD rfl hT hq
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one hexp ⊤ _
  let eL : ↥Mp ≃* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    (autSubEquivOfFaithful hLs hfaith).trans
      (B5.secEquiv (autSub Mp V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful)
  have hgood := ksb_good h42 h45 hsv hb4 hqhat hqs (KsCover.of_mulEquiv eL hKs)
  have hLZ : Mp ≤ stabSub (V ⊓ fixV Mp) :=
    le_stabSub_of_le_fixV (inf_le_right.trans (fixV_anti le_rfl))
  rcases hgood with ⟨n, hn, h⟩ | ⟨f, h⟩ | ⟨a, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩
  · exact Or.inl ⟨n, hn, binaryNaturalSL_of_autSub hLs hLZ inf_le_left hfaith
      (InternalSec.binaryNaturalSL_of_autSec hQ.stabKC hQ.faithful h)⟩
  · exact Or.inr (Or.inl ⟨f, binaryNaturalSz_of_autSub hLs hLZ inf_le_left hfaith
      (InternalSec.binaryNaturalSz_of_autSec hQ.stabKC hQ.faithful h)⟩)
  · obtain ⟨K, hKf, hKfin, hc, hr⟩ :=
      InternalSec.binaryNaturalSU3_of_autSec hQ.stabKC hQ.faithful h
    exact Or.inr (Or.inr (Or.inl ⟨a, K, hKf, hKfin, hc,
      FFModel.Realizes.of_autSub hLs hLZ inf_le_left hfaith hr⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, binaryNaturalSL_of_autSub hLs hLZ inf_le_left hfaith
      (InternalSec.binaryNaturalSL_of_autSec hQ.stabKC hQ.faithful h)⟩)))
  · obtain ⟨K, hKf, hKfin, hc, hr⟩ :=
      InternalSec.binaryNaturalSp4_of_autSec hQ.stabKC hQ.faithful h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn, K, hKf, hKfin, hc,
      FFModel.Realizes.of_autSub hLs hLZ inf_le_left hfaith hr⟩)))

end Main

end S153L

end CFSG.Quasithin
