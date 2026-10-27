module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrJ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrK
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrD
public import CFSG.Quasithin.Vol2.Ch11SecBHBMain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem card_star_mul_card_inf {X H L : Subgroup G} (hLH : L ≤ H) :
    Nat.card (E2.star X H L) * Nat.card (L ⊓ kerIn X H : Subgroup G) = Nat.card L := by
  set L' := L.subgroupOf H
  let f : ↥L' →* E2.StarQuot X H := (starMk X H).comp L'.subtype
  have hrange : f.range = E2.star X H L := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  let e : f.ker ≃ ↥(L ⊓ kerIn X H : Subgroup G) :=
    { toFun := fun l => ⟨((l.1 : ↥H) : G), Subgroup.mem_subgroupOf.mp l.1.2,
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp l.2))⟩
      invFun := fun y => ⟨⟨⟨y.1, hLH y.2.1⟩, Subgroup.mem_subgroupOf.mpr y.2.1⟩,
        MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr
          (Subgroup.mem_subgroupOf.mpr y.2.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : Nat.card ↥L' = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥L' = Nat.card L := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
  rw [← hrange, ← Nat.card_congr e, ← h2, h1]

theorem mem_sup_of_star {X H K : Subgroup G} {x : G} (hx : x ∈ H)
    (h : starMk X H ⟨x, hx⟩ ∈ E2.star X H K) : x ∈ K ⊔ kerIn X H := by
  obtain ⟨k, hk, hke⟩ := h
  have h1 : k⁻¹ * ⟨x, hx⟩ ∈ (kerIn X H).subgroupOf H := by
    rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H), MonoidHom.mem_ker, map_mul,
      map_inv, inv_mul_eq_one]
    exact hke
  have h2 : ((k : ↥H) : G)⁻¹ * x ∈ kerIn X H := Subgroup.mem_subgroupOf.mp h1
  have := Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk) :
    ((k : ↥H) : G) ∈ K ⊔ kerIn X H) (Subgroup.mem_sup_right h2)
  simpa using this

theorem le_of_odd {H K B : Subgroup G} (hBH : B ≤ H) (hBo : Odd (Nat.card B))
    (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K) : B ≤ K := by
  intro b hb
  obtain ⟨k, hk⟩ := h2 b (hBH hb)
  refine B6.mem_of_pow_mem_of_coprime hk (Nat.Coprime.pow_right _ ?_)
  exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hb))

theorem isPGroup_autOn {T B : Subgroup G} (hT2 : IsPGroup 2 T) : IsPGroup 2 (autOn T B) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hT2

variable [Finite G]

theorem case2a_false (hBC : FactBorelCartan) {H T X K B : Subgroup G}
    (hXH : X ≤ H) (hTX : T ≤ X) (hTXs : IsSylowTwoOf T X)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T)
    (hBen : E2.IsBenderOf 2 ↥(E2.star X H K))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)))
    (hB : Lin2.IsHallTwoPrimeOf B X) (hB9 : Nat.card B = 9) (hA : 8 ≤ Nat.card (autOn T B)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 := hTXs.2.1
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have h2K : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K :=
    B6.isTwoQuotient_of_sup_eq hT2 hHKn (by rw [hHK, sup_comm])
  have hBH : B ≤ H := hB.1.trans hXH
  have hBK : B ≤ K := le_of_odd hBH hB.2.1 h2K
  have hK9 : ¬ 9 ∣ Nat.card (E2.star X H K) := by
    obtain ⟨-, h | h | h⟩ := hBen
    · rw [card_of_isPSL_two_two_two h]
      norm_num
    · exact absurd h not_isSz_two
    · rw [card_of_isPSU_three_two_two h]
      norm_num
  have hcB := card_star_mul_card_inf (X := X) hBH
  rw [hB9] at hcB
  have hdvdK : Nat.card (E2.star X H B) ∣ Nat.card (E2.star X H K) :=
    Subgroup.card_dvd_of_le (star_mono hBK)
  obtain ⟨d, hd, hdo⟩ := exists_borel_elt hBC le_rfl (Or.inl hBen) hBor
  have hdX : d ∈ E2.star X H X := star_mono inf_le_left hd
  have h3X : 3 ∣ Nat.card (E2.star X H X) := by
    have h := orderOf_dvd_natCard (⟨d, hdX⟩ : ↥(E2.star X H X))
    rwa [Subgroup.orderOf_mk, hdo] at h
  have hcX := card_star_mul_card_inf (X := X) hXH
  rw [card_eq_card_mul_card hTXs hB, hB9] at hcX
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT2
  rw [ha] at hcX
  have hBJ3 : Nat.card (B ⊓ kerIn X H : Subgroup G) = 3 := by
    have hm : Nat.card (E2.star X H B) ∣ 9 := Dvd.intro _ hcB
    have hm9 : Nat.card (E2.star X H B) ≠ 9 := fun h => hK9 (h ▸ hdvdK)
    have hcases : Nat.card (E2.star X H B) = 1 ∨ Nat.card (E2.star X H B) = 3 := by
      have := Nat.le_of_dvd (by norm_num) hm
      interval_cases h : Nat.card (E2.star X H B) <;> simp_all
    rcases hcases with h1 | h3
    · exfalso
      rw [h1, one_mul] at hcB
      have hBJ : B ⊓ kerIn X H = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcB, hB9])
      have h9 : 9 ∣ Nat.card (X ⊓ kerIn X H : Subgroup G) := by
        rw [← hB9, ← hBJ]
        exact Subgroup.card_dvd_of_le (inf_le_inf_right _ hB.1)
      obtain ⟨q, hq⟩ := h9
      rw [hq] at hcX
      have h4 : Nat.card (E2.star X H X) * q = 2 ^ a := by
        have : Nat.card (E2.star X H X) * q * 9 = 2 ^ a * 9 := by rw [← hcX]; ring
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
      have h5 : 3 ∣ 2 ^ a := h3X.trans (Dvd.intro _ h4)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5) (by norm_num)
    · rw [h3] at hcB
      omega
  set C := (B ⊓ kerIn X H).subgroupOf B
  have hC3 : Nat.card C = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ kerIn X H ≤ B)).toEquiv,
      hBJ3]
  have hAC : ∀ a ∈ autOn T B, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ c hc
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    refine ⟨(conjAct B x c).2, ?_⟩
    have hxH : ((x : Subgroup.normalizer (B : Set G)) : G) ∈ H :=
      hTX.trans hXH (Subgroup.mem_subgroupOf.mp hx)
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn X H hxH) c).mp hc.2
    have hconj : ((conjAct B x c : B) : G) = ((x : Subgroup.normalizer (B : Set G)) : G) * c *
        ((x : Subgroup.normalizer (B : Set G)) : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe B (Subgroup.inclusion le_rfl x) c
    rw [hconj]
    exact this
  have h4 := card_le_four_of_stab hB9 C hC3 (autOn T B) (isPGroup_autOn hT2) hAC
  omega

omit [Finite G] in
theorem star_perfect {X H K : Subgroup G} (hKH : K ≤ H) (hK : ⁅K, K⁆ = K) :
    ⁅E2.star X H K, E2.star X H K⁆ = E2.star X H K := by
  have h1 : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH, hK]
  rw [E2.star, ← Subgroup.map_commutator, h1]

theorem case2b_false (hW2 : FactOutL34Sp44) (hFB : Ch11.SecB.FactBorelComm)
    {H T X K B : Subgroup G} (hmin : MinParabolic H T X) (hXH : X ≤ H) (hTX : T ≤ X)
    (hTXs : IsSylowTwoOf T X) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ T)
    (hJ : ∀ x : G, x ∈ kerIn X H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (htype : IsPSL 3 2 2 ↥(E2.star X H K) ∨ IsPSp4 2 2 ↥(E2.star X H K))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)))
    (hB : Lin2.IsHallTwoPrimeOf B X) (hA : 8 ≤ Nat.card (autOn T B)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 := hTXs.2.1
  have hTH : T ≤ H := hTX.trans hXH
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKperf : ⁅K, K⁆ = K := (show quasithinIsCComponent K H from hKc).2.1
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have h2K : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K :=
    B6.isTwoQuotient_of_sup_eq hT2 hHKn (by rw [hHK, sup_comm])
  have hBH : B ≤ H := hB.1.trans hXH
  have hBK : B ≤ K := le_of_odd hBH hB.2.1 h2K
  have hKn : (E2.star X H K).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHKn).map _
      (QuotientGroup.mk'_surjective _)
  have h2 : ∀ x : E2.StarQuot X H, ∃ k : ℕ, x ^ 2 ^ k ∈ E2.star X H K := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn X H).subgroupOf H) x
    obtain ⟨k, hk⟩ := h2K h h.2
    exact ⟨k, ⟨h ^ 2 ^ k, Subgroup.mem_subgroupOf.mpr (by simpa using hk), by rw [map_pow]⟩⟩
  have hsimp : IsSimpleGroup ↥(E2.star X H K) := by
    rcases htype with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2
    · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 2 h
  have hZ : ∀ y ∈ E2.star X H K, (∀ z ∈ E2.star X H K, y * z = z * y) → y = 1 := by
    intro y hy hz
    have hc : (⟨y, hy⟩ : ↥(E2.star X H K)) ∈ Subgroup.center ↥(E2.star X H K) :=
      Subgroup.mem_center_iff.mpr fun z => Subtype.ext (hz z z.2).symm
    have := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(E2.star X H K)) with h | h
    · rw [h, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    · exfalso
      have hcomm : ∀ a b : ↥(E2.star X H K), a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      have hbot : ⁅E2.star X H K, E2.star X H K⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [star_perfect hKH hKperf] at hbot
      have hnt : Nontrivial ↥(E2.star X H K) := hsimp.toNontrivial
      rw [Subgroup.nontrivial_iff_ne_bot] at hnt
      exact hnt hbot
  have hC := centralizer_eq_bot_of hZ h2 (eq_bot_of_normal_star hmin)
  have hidx := index_le_four_of_dvd hC h2 (hW2 _ htype)
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hOJ : pCoreOf 2 H ≤ kerIn X H := Ch11.SecB.le_kerIn_of_le_normalizer (hQT.trans hTX) hHO
  have hOK : pCoreOf 2 K ≤ kerIn X H :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)).trans hOJ
  have hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
    intro k hk hkJ y hy
    refine Ch11.SecB.inf_pCoreOf_le_pCoreOf hKH ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy)
      (K.inv_mem hk)) (K.inv_mem hy), ?_⟩
    exact ((hJ k).mp hkJ).2 y (Subgroup.mem_sup_left hy)
  have hR := Ch11.SecB.isPGroup_commutator_inf_of_isBorelIn hFB hKH hKperf hOK hcent le_rfl
    (Or.inr htype) hBor
  have hle := card_autOn_le_index_of (Y := E2.star X H K) hTH fun x hxT hxN hxK => by
    have hJle : kerIn X H ≤ K ⊔ pCoreOf 2 H := fun j hj => ((hJ j).mp hj).1
    have hx1 : x ∈ K ⊔ pCoreOf 2 H := sup_le le_sup_left hJle (mem_sup_of_star (hTH hxT) hxK)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _
      (hKH.trans hHO)] at hx1
    obtain ⟨k, hk, q, hq, rfl⟩ := hx1
    have hkT : k ∈ T := by
      have := T.mul_mem hxT (T.inv_mem (hQT hq))
      simpa using this
    exact mul_mem_centralizer hR (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      ((inf_le_left.trans hXH).trans hHO) (le_inf hB.1 hBK) hB.2.1 ⟨hTX hkT, hk⟩ hq hxN
  omega

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
