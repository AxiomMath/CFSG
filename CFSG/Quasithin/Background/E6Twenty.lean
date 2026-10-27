module

public import CFSG.Quasithin.Background.E6TwentyB
public import CFSG.Quasithin.Background.E6TwentyA

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Tools

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem exists_z_charTwo (h : HypE61 T M V) :
    ∃ z ∈ V, z ≠ 1 ∧ CharTwo (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzV, hzT, hz1⟩ : ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
    have hT2 : IsPGroup 2 T := h.sylow.1
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h.normal
    have hne : V.subgroupOf T ≠ ⊥ := by
      intro h0
      apply h.ne_bot
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h0, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    refine ⟨y, hy.1, ⟨y.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)⟩, fun h1 => hy1 ?_⟩
    exact Subtype.ext (Subtype.ext h1)
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz : Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]
    exact (inf_eq_right.2 ((centralizer_zpowers_eq z).symm ▸
      Subgroup.centralizer_le_normalizer _)).symm
  have hTsyl : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZT : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_zpowers z, hzT⟩
    rw [h0] at this
    exact this
  have hNz := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hTsyl hZ2 hZT
  refine ⟨z, hzV, hz1, ?_⟩
  rw [hCz]
  exact CT.CharTwo.inf_centralizer hNz Subgroup.le_normalizer hZ2

theorem oddCoreIn_eq_bot_of_mem {W : Subgroup G} (hV : IsElemAbelian 2 V) (hWV : W ≤ V)
    {z : G} (hzW : z ∈ W) (hz : CharTwo (Subgroup.centralizer ({z} : Set G))) :
    oddCoreIn (Subgroup.centralizer (W : Set G)) = ⊥ := by
  have hWz : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (B2F.isElemAbelian_comm hV (hWV hw) (hWV hzW))
  have h1 := CT.CharTwo.inf_centralizer hz hWz ((B2F.isPGroup_of_isElemAbelian hV).to_le hWV)
  rw [inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzW))] at h1
  exact oddCoreIn_eq_bot_of_charTwo' h1

theorem pCoreOf_le_oddCoreIn {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (H : Subgroup G) :
    pCoreOf p H ≤ oddCoreIn H := by
  refine le_oddCoreIn_of_odd (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p H)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf p H) ?_
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup p H)
  rw [hn]
  exact (hp.out.odd_of_ne_two hp2).pow

omit [Finite G] in
theorem le_pCoreOf_of_comm {p : ℕ} {A Y : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hYA : Y ≤ A) (hY : IsPGroup p Y) : Y ≤ pCoreOf p A := by
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf p Y A hYA ?_ hY
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYA]
  intro a ha
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun y hy => hA _ (hYA hy) _ ha)

omit [Finite G] in
theorem pCoreOf_oddCoreIn_le (p : ℕ) (H : Subgroup G) : pCoreOf p (oddCoreIn H) ≤ pCoreOf p H := by
  have hle : pCoreOf p (oddCoreIn H) ≤ H :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p _).trans (E3.oddCoreIn_le H)
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf p _ H hle ?_
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup p _)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact (E3.le_normalizer_oddCoreIn H).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf p _)

omit [Finite G] in
theorem conjugate_pCoreOf_centralizer (p : ℕ) (W : Subgroup G) (g : G) :
    CFSG.conjugate (pCoreOf p (Subgroup.centralizer (W : Set G))) g =
      pCoreOf p (Subgroup.centralizer ((CFSG.conjugate W g : Subgroup G) : Set G)) := by
  rw [← BenderBranch.conjugate_centralizer]
  unfold CFSG.conjugate
  exact (pCoreOf_map_equiv p (MulAut.conj g⁻¹) _).symm

theorem exists_le_mQuot_eq_three (hV2 : IsPGroup 2 V) (h6 : 6 ≤ E3.mQuot V ⊥)
    {B : Subgroup G} (hBV : B ≤ V) (hB : E3.mQuot V B ≤ 3) :
    ∃ U₀ : Subgroup G, U₀ ≤ B ∧ E3.mQuot V U₀ = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := E3.mQuot V ⊥ with hn
  have hVc : Nat.card V = 2 ^ n := by
    have h1 := E3.relIndex_eq_two_pow hV2 ⊥
    rwa [Subgroup.relIndex_bot_left] at h1
  have hBc : Nat.card B * 2 ^ E3.mQuot V B = 2 ^ n := by
    have h1 := Subgroup.relIndex_mul_card B V
    rw [inf_eq_left.2 hBV, E3.relIndex_eq_two_pow hV2] at h1
    rw [← hVc, ← h1, mul_comm]
  have hdvd : 2 ^ (n - 3) ∣ Nat.card B := by
    have h2 : 2 ^ (n - 3) * 2 ^ 3 = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have h3 : 2 ^ E3.mQuot V B ∣ 2 ^ 3 := pow_dvd_pow 2 hB
    obtain ⟨c, hc⟩ := h3
    refine ⟨c, ?_⟩
    have hpos : 0 < 2 ^ E3.mQuot V B := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hBc, ← h2, hc]
    ring
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 2 hdvd
  refine ⟨K.map B.subtype, Subgroup.map_subtype_le K, ?_⟩
  have hKc : Nat.card (K.map B.subtype) = 2 ^ (n - 3) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hK]
  have h1 := Subgroup.relIndex_mul_card (K.map B.subtype) V
  rw [inf_eq_left.2 ((Subgroup.map_subtype_le K).trans hBV), hKc, hVc] at h1
  have h2 : (K.map B.subtype).relIndex V = 2 ^ 3 := by
    have h3 : 2 ^ 3 * 2 ^ (n - 3) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hpos : 0 < 2 ^ (n - 3) := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)
  unfold E3.mQuot
  rw [h2]
  exact padicValNat.prime_pow 3

end Tools

theorem e620_of (h311 : Theorem311Stmt) (h619 : E619Stmt) : E620Stmt := by
  intro G _ _ T M V U hV h h15 hUV hU1
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hO
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := by
    intro hle
    apply hO
    have h1 := oddCoreIn_eq_bot_of_charTwo' (e6_6_one h hUV)
    rwa [inf_eq_right.2 hle] at h1
  obtain ⟨hr, hm, -⟩ := e6_16_one hV h h15 hUV hU1 hUM
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr).2
  obtain ⟨z, hzV, -, hzC⟩ := exists_z_charTwo h
  have hzW : ∀ W : Subgroup G, W ≤ V →
      oddCoreIn (Subgroup.centralizer (W : Set G)) ≠ ⊥ → z ∉ W :=
    fun W hWV hW hzW => hW (oddCoreIn_eq_bot_of_mem hV hWV hzW hzC)
  have hX : ∀ U₀ : Subgroup G, U₀ ≤ V → E3.mQuot V U₀ = 3 → z ∉ U₀ →
      ∃ X : Subgroup G, X ≤ Subgroup.centralizer (U₀ : Set G) ∧
        V ≤ Subgroup.normalizer (X : Set G) ∧
        (∀ B : Subgroup G, U₀ ≤ B → B ≤ V → B ≠ U₀ →
          X ⊓ Subgroup.centralizer (B : Set G) = oddCoreIn (Subgroup.centralizer (B : Set G))) ∧
        ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro U₀ hU₀V hU₀3 hzU₀
    obtain ⟨X, hXU, hXN, -, hXC, hXab⟩ := e620_functor h619 hV h h15 hU₀V hU₀3
    exact ⟨X, hXU, hXN, hXC, hXab z hzV hzU₀ (oddCoreIn_eq_bot_of_mem hV
      (sup_le hU₀V (Subgroup.zpowers_le.2 hzV)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      hzC)⟩
  have hOodd := E3.odd_card_oddCoreIn' (Subgroup.centralizer (U : Set G))
  have hO1 : Nat.card (oddCoreIn (Subgroup.centralizer (U : Set G))) ≠ 1 := fun h1 =>
    hO (Subgroup.card_eq_one.1 h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hO1
  have hp2 : p ≠ 2 := fun h2 =>
    (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 (h2 ▸ hpdvd))
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G → Subgroup G := fun B => pCoreOf p (Subgroup.centralizer (B : Set G))
    with hPdef
  have hY : ∀ U₀ : Subgroup G, U₀ ≤ V → E3.mQuot V U₀ = 3 → z ∉ U₀ →
      ∃ Y : Subgroup G, (∀ B : Subgroup G, U₀ ≤ B → B ≤ V → B ≠ U₀ → P B ≤ Y) ∧
        (∃ B : Subgroup G, B ≤ V ∧ E3.mQuot V B ≤ 2 ∧ Y ≤ P B) ∧
        Y ≤ ⨆ (W : Subgroup G) (_ : W ≤ V ∧ E3.mQuot V W = 1), P W := by
    intro U₀ hU₀V hU₀3 hzU₀
    obtain ⟨X, hXU, hXN, hXC, hXab⟩ := hX U₀ hU₀V hU₀3 hzU₀
    set Y := pCoreOf p X with hYdef
    have hYX : Y ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p X
    have hYp : IsPGroup p Y := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup p X
    have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb => hXab _ (hYX ha) _ (hYX hb)
    have hOB : ∀ B : Subgroup G, U₀ ≤ B → B ≤ V → B ≠ U₀ →
        ∀ a ∈ oddCoreIn (Subgroup.centralizer (B : Set G)),
          ∀ b ∈ oddCoreIn (Subgroup.centralizer (B : Set G)), a * b = b * a := by
      intro B h1 h2 h3 a ha b hb
      rw [← hXC B h1 h2 h3] at ha hb
      exact hXab _ ha.1 _ hb.1
    have hPY : ∀ B : Subgroup G, U₀ ≤ B → B ≤ V → B ≠ U₀ → P B ≤ Y := by
      intro B h1 h2 h3
      refine le_pCoreOf_of_comm hXab ?_
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup p _)
      refine (pCoreOf_le_oddCoreIn hp2 _).trans ?_
      rw [← hXC B h1 h2 h3]
      exact inf_le_left
    have hXV : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
      rw [hXC V hU₀V le_rfl (fun he => by rw [he, E3.mQuot_self] at hU₀3; omega)]
      exact oddCoreIn_centralizer_V h
    have hU₀1 : U₀ ≠ ⊥ := by
      rintro rfl
      omega
    refine ⟨Y, hPY, ?_, ?_⟩
    ·
      have hVY : V ≤ Subgroup.normalizer (Y : Set G) :=
        hXN.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf
          p X)
      have hrk : CFSG.Open.pRank p Y ≤ 2 := by
        have h1 : Y ≤ Subgroup.normalizer (U₀ : Set G) :=
          hYX.trans (hXU.trans (Subgroup.centralizer_le_normalizer _))
        exact (CFSG.SectionRank.pRank_mono hp.one_lt h1).trans
          ((A1b.pRank_le_evenRank hp hp2 ⟨U₀, hU₀1, hV2.to_le hU₀V, rfl⟩).trans h.qtke.2.2)
      have hB2 := mQuot_inf_centralizer_le_two hp2 hV hYp hYab hVY hrk
      set B := V ⊓ Subgroup.centralizer (Y : Set G) with hBdef
      have hU₀B : U₀ ≤ B := le_inf hU₀V (Subgroup.le_centralizer_iff.1 (hYX.trans hXU))
      have hBne : B ≠ U₀ := fun he => by rw [he, hU₀3] at hB2; omega
      have hYB : Y ≤ Subgroup.centralizer (B : Set G) :=
        Subgroup.le_centralizer_iff.1 inf_le_right
      refine ⟨B, inf_le_left, hB2, ?_⟩
      have hYO : Y ≤ oddCoreIn (Subgroup.centralizer (B : Set G)) := by
        rw [← hXC B hU₀B inf_le_left hBne]
        exact le_inf hYX hYB
      exact (le_pCoreOf_of_comm (hOB B hU₀B inf_le_left hBne) hYO hYp).trans
        (pCoreOf_oddCoreIn_le p _)
    ·
      have hYodd : Odd (Nat.card Y) := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hYp
        rw [hn]
        exact (hp.odd_of_ne_two hp2).pow
      have hVY : V ≤ Subgroup.normalizer (Y : Set G) :=
        hXN.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf
          p X)
      refine (E3.le_iSup_hyperplane_inf_centralizer hYodd hV h.ne_bot hVY).trans
        (iSup₂_le fun S hS => ?_)
      obtain ⟨hSV, hSc⟩ := hS
      have hS1 : E3.mQuot V S = 1 := mQuot_eq_one_of_card hSV hSc
      by_cases hU₀S : U₀ ≤ S
      · have hSne : S ≠ U₀ := fun he => by rw [he, hU₀3] at hS1; omega
        refine le_trans ?_ (le_iSup₂_of_le S ⟨hSV, hS1⟩ le_rfl)
        have hYO : Y ⊓ Subgroup.centralizer (S : Set G) ≤
            oddCoreIn (Subgroup.centralizer (S : Set G)) := by
          rw [← hXC S hU₀S hSV hSne]
          exact inf_le_inf_right _ hYX
        exact (le_pCoreOf_of_comm (hOB S hU₀S hSV hSne) hYO (hYp.to_le inf_le_left)).trans
          (pCoreOf_oddCoreIn_le p _)
      · have hSU : S ⊔ U₀ = V := sup_eq_of_card hSV hU₀V hSc hU₀S
        have hle : Y ⊓ Subgroup.centralizer (S : Set G) ≤ X ⊓ Subgroup.centralizer (V : Set G) := by
          rintro y ⟨hyY, hyS⟩
          refine ⟨hYX hyY, ?_⟩
          rw [← hSU, centralizer_sup_eq]
          exact ⟨hyS, hXU (hYX hyY)⟩
        rw [hXV] at hle
        exact hle.trans bot_le
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨U₄, hU₄mem, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun B : Subgroup G => B ≤ V ∧ E3.mQuot V B ≤ 2)
    (fun B => Nat.card (P B)) ⟨U, by simp [hUV, hU1]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU₄mem hmax
  obtain ⟨hU₄V, hU₄2⟩ := hU₄mem
  set Y₁ := P U₄ with hY₁def
  have hPU : P U ≠ ⊥ := by
    have hzU : z ∉ U := hzW U hUV hO
    obtain ⟨U₀, hU₀U, hU₀3⟩ := exists_le_mQuot_eq_three hV2 h6 hUV (by omega)
    have hU₀V : U₀ ≤ V := hU₀U.trans hUV
    obtain ⟨X, -, -, hXC, hXab⟩ := hX U₀ hU₀V hU₀3 (fun h0 => hzU (hU₀U h0))
    have hUne : U ≠ U₀ := fun he => by rw [he, hU₀3] at hU1; omega
    have hOab : ∀ a ∈ oddCoreIn (Subgroup.centralizer (U : Set G)),
        ∀ b ∈ oddCoreIn (Subgroup.centralizer (U : Set G)), a * b = b * a := by
      intro a ha b hb
      rw [← hXC U hU₀U hUV hUne] at ha hb
      exact hXab _ ha.1 _ hb.1
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(oddCoreIn (Subgroup.centralizer (U : Set G)))) p hpdvd
    have hyp : IsPGroup p (Subgroup.zpowers (y : G)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one])
    have hle : Subgroup.zpowers (y : G) ≤ P U :=
      (le_pCoreOf_of_comm hOab (Subgroup.zpowers_le.2 y.2) hyp).trans (pCoreOf_oddCoreIn_le p _)
    intro h0
    have h1 : (y : G) ∈ P U := hle (Subgroup.mem_zpowers _)
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
    rw [h1, orderOf_one] at h2
    exact hp.one_lt.ne h2
  have hY₁1 : Y₁ ≠ ⊥ := by
    intro h0
    have h1 := hmax U ⟨hUV, by omega⟩
    rw [h0, Subgroup.card_bot] at h1
    exact hPU (Subgroup.card_eq_one.1 (le_antisymm h1 Nat.card_pos))
  have hY₁U₄ : Y₁ ≤ Subgroup.centralizer (U₄ : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p _
  have hY₁O : Y₁ ≤ oddCoreIn (Subgroup.centralizer (U₄ : Set G)) := pCoreOf_le_oddCoreIn hp2 _
  have hOU₄ : oddCoreIn (Subgroup.centralizer (U₄ : Set G)) ≠ ⊥ := fun h0 =>
    hY₁1 (le_bot_iff.1 (h0 ▸ hY₁O))
  have hzU₄ : z ∉ U₄ := hzW U₄ hU₄V hOU₄
  have hB : ∀ W : Subgroup G, W ≤ V → E3.mQuot V W = 1 → P W ≤ Y₁ := by
    intro W hWV hW1
    by_contra hnot
    have hPW1 : P W ≠ ⊥ := fun h0 => hnot (h0 ▸ bot_le)
    have hzW' : z ∉ W := hzW W hWV fun h0 =>
      hPW1 (le_bot_iff.1 (h0 ▸ pCoreOf_le_oddCoreIn hp2 _))
    have hm3 : E3.mQuot V (U₄ ⊓ W) ≤ 3 := by
      have := mQuot_inf_le (U := U₄) (U' := W) hV2
      omega
    obtain ⟨U₀, hU₀le, hU₀3⟩ := exists_le_mQuot_eq_three hV2 h6 (inf_le_left.trans hU₄V) hm3
    have hU₀V : U₀ ≤ V := hU₀le.trans (inf_le_left.trans hU₄V)
    obtain ⟨Y, hPY, ⟨B, hBV, hB2, hYB⟩, -⟩ :=
      hY U₀ hU₀V hU₀3 (fun h0 => hzW' (hU₀le h0).2)
    have hU₄ne : U₄ ≠ U₀ := fun he => by rw [he, hU₀3] at hU₄2; omega
    have hWne : W ≠ U₀ := fun he => by rw [he, hU₀3] at hW1; omega
    have h1 : Y₁ ≤ Y := hPY U₄ (hU₀le.trans inf_le_left) hU₄V hU₄ne
    have h2 : P W ≤ Y := hPY W (hU₀le.trans inf_le_right) hWV hWne
    have hlt : Y₁ < Y := lt_of_le_of_ne h1 fun he => hnot (he ▸ h2)
    have h3 := Subgroup.card_lt_of_lt hlt
    have h4 := Subgroup.card_le_of_le hYB
    have h5 := hmax B ⟨hBV, hB2⟩
    omega
  set Ŷ := ⨆ (W : Subgroup G) (_ : W ≤ V ∧ E3.mQuot V W = 1), P W with hŶdef
  have hC : Y₁ ≤ Ŷ := by
    obtain ⟨U₀, hU₀le, hU₀3⟩ := exists_le_mQuot_eq_three hV2 h6 hU₄V (by omega)
    have hU₀V : U₀ ≤ V := hU₀le.trans hU₄V
    obtain ⟨Y, hPY, -, hYgen⟩ := hY U₀ hU₀V hU₀3 (fun h0 => hzU₄ (hU₀le h0))
    have hU₄ne : U₄ ≠ U₀ := fun he => by rw [he, hU₀3] at hU₄2; omega
    exact (hPY U₄ hU₀le hU₄V hU₄ne).trans hYgen
  have hYeq : Y₁ = Ŷ := le_antisymm hC (iSup₂_le fun W hW => hB W hW.1 hW.2)
  have hTY : T ≤ Subgroup.normalizer (Y₁ : Set G) := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (V : Set G) := h.normal ht
    have hle : CFSG.conjugate Ŷ t ≤ Ŷ := by
      unfold CFSG.conjugate
      rw [hŶdef, Subgroup.map_iSup]
      refine iSup_le fun W => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hW => ?_
      have h1 := conjugate_pCoreOf_centralizer p W t
      unfold CFSG.conjugate at h1
      rw [h1]
      exact le_iSup₂_of_le (CFSG.conjugate W t)
        ⟨conjugate_le_of_mem_normalizer hW.1 htN, (mQuot_conjugate htN).trans hW.2⟩ le_rfl
    have heq : CFSG.conjugate Ŷ t = Ŷ :=
      Subgroup.eq_of_le_of_card_ge hle (BenderBranch.card_conjugate Ŷ t).ge
    rw [hYeq]
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq
  set W := V ⊓ Subgroup.centralizer (Y₁ : Set G) with hWdef
  have hU₄W : U₄ ≤ W := le_inf hU₄V (Subgroup.le_centralizer_iff.1 hY₁U₄)
  have hW2 : E3.mQuot V W ≤ 2 := (E3.mQuot_mono hU₄W).trans hU₄2
  have hW1 : W ≠ ⊥ := fun h0 => by rw [h0] at hW2; omega
  have hU₄M : ¬ Subgroup.centralizer (U₄ : Set G) ≤ M := by
    intro hle
    apply hOU₄
    have h1 := oddCoreIn_eq_bot_of_charTwo' (e6_6_one h hU₄V)
    rwa [inf_eq_right.2 hle] at h1
  have hU₄1 : U₄ ≠ ⊥ := fun h0 => by rw [h0] at hU₄2; omega
  have hU₄Γ : U₄ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₄V hU₄1 hU₄M (by omega)
  have hY₁M : ¬ Y₁ ≤ M := by
    intro hle
    apply hY₁1
    have h1 := e6_9_one h hU₄Γ
    rw [eq_bot_iff, ← h1]
    exact le_inf hY₁O hle
  have hWM : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle =>
    hY₁M ((Subgroup.le_centralizer_iff.1 inf_le_right).trans hle)
  have hWΓ : W ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h inf_le_left hW1 hWM (by omega)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    B2F.le_normalizer_inf h.normal (B2F.le_normalizer_centralizer hTY)
  exact hWM (e6_13 h311 h inf_le_left hW1 hWΓ.2.2.2 hTW)

end E6

end CFSG.Quasithin
