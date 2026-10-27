module

public import CFSG.Quasithin.Background.C48SporShape
public import CFSG.Quasithin.Background.C48SporCover
public import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.Background.C31SporJ
public import CFSG.Quasithin.Background.C48AsmSteps
public import CFSG.Quasithin.Background.C48SporK

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centerOf_iff {K : Subgroup G} {x : G} :
    x ∈ centerOf K ↔ ∃ hx : x ∈ K, (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
  constructor
  · rintro ⟨hxK, hxC⟩
    refine ⟨hxK, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hxC g g.2
  · rintro ⟨hxK, hx⟩
    refine ⟨hxK, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)

omit [Finite G] in
theorem isPGroup_center_of {K : Subgroup G} (hZ : IsPGroup 2 ↥(centerOf K)) :
    IsPGroup 2 ↥(Subgroup.center ↥K) := by
  rintro ⟨z, hz⟩
  obtain ⟨k, hk⟩ := hZ ⟨z, mem_centerOf_iff.2 ⟨z.2, hz⟩⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_center {K V : Subgroup G} (hVK : V ≤ K)
    (hZ : Subgroup.center ↥K = ⊥) : V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hvC⟩
  have : (⟨v, hVK hv⟩ : ↥K) ∈ Subgroup.center ↥K := (mem_centerOf_iff.1 ⟨hVK hv, hvC⟩).2
  rw [hZ, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

theorem c48SporStep_core {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (h31 : C31Basic H R M L V K) (hL : L = conjClosure L M)
    {s : TauCeti.SporadicName} (hInsp : InspC31SporadicAtJ s)
    (hJ : s = .J4 → C31SporJ.J4Cond (img (sporN H K) R) (img (sporN H K) M))
    (hsK : IsSporadic s (↥K ⧸ Subgroup.center ↥K))
    (hZ : Subgroup.center ↥K = ⊥ ∨
      ((Nat.card (ModO2 (conjClosure L M)) ∣ 60 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 360 ∨
          Nat.card (ModO2 (conjClosure L M)) ∣ 168 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 6048) ∧
        (IsPSL 3 2 1 (ModO2 L) → V ⊓ centerOf K = ⊥))) :
    (C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
        C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
        C48Case7 H R M L V K) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 L) →
        IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2 := by
  have hKX := K_le_sporX (H := H) hK.1
  have hsimp := isSimpleGroup_kStar hK
  have hperf := commutator_kStar hK
  have hL0 : L = conjClosure L M := hL
  have hM0ne : img (sporN H K) (conjClosure L M) ≠ ⊥ := fun hb =>
    img_V_ne_bot h h31 (le_bot_iff.mp (hb ▸ img_mono h.V_le))
  obtain ⟨-, hC48, hbound⟩ := hInsp (↥(sporX H K) ⧸ sporN H K) (img (sporN H K) K)
    (img (sporN H K) (conjClosure L M)) (img (sporN H K) R) (img (sporN H K) M)
    (img (sporN H K) V) (img_K_normal H K) (IsSporadic.of_mulEquiv (kStarEquiv hKX) hsK)
    (centralizer_kStar_eq_bot (commutator_eq_of_isComponentOf hK) hKX) (img_mono h31.1)
    (img_M0_perfect h h31) hM0ne (exists_cComp_img h h31) (isPGroup_img h.pgroup)
    (img_mono h.le_M) (img_le_normalizer (le_normalizer_conjClosure L M))
    (img_le_normalizer (c2_9_two h).1) (img_isSylowTwoOf h h31) (img_mono h.V_le)
    (img_V_ne_bot h h31) (isElemAbelian_img h.V_elem) (img_V_comm h h31) (img_V_le_center h h31)
    (normalizer_inf_le_img_M h h31) (normalizer_img_R_le h h31) (not_img_K_le h hK h31) hJ
  have hcard : Nat.card (ModO2 (conjClosure L M)) =
      Nat.card (ModO2 (img (sporN H K) (conjClosure L M))) :=
    Nat.card_congr (modO2EquivL h h31).toEquiv
  have hshape : ∀ t : ℕ, (t = 2520 ∨ t = 1080 ∨ t = 20160 ∨ t = 9999360) →
      Nat.card (ModO2 (img (sporN H K) (conjClosure L M))) = t → Subgroup.center ↥K = ⊥ := by
    intro t ht htc
    rcases hZ with hZ | ⟨hdiv, -⟩
    · exact hZ
    · exfalso
      rw [hcard, htc] at hdiv
      rcases ht with rfl | rfl | rfl | rfl <;> revert hdiv <;> decide
  refine ⟨?_, ?_⟩
  · rcases hC48 with c1 | c2 | c3 | c4 | c5 | c6 | c7
    ·
      left
      obtain ⟨n, hn, hmod | hmod | hthird⟩ := c1
      · exact c48Case1_of_img h h31 hL hn (Or.inl hmod)
      · exact c48Case1_of_img h h31 hL hn (Or.inr hmod)
      · exact absurd hthird.2.1 (not_isC134Case_two (img_K_normal H K) hperf)
    ·
      right; left
      have hVK : V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
        rcases hZ with hZ | ⟨hdiv, hcov⟩
        · exact inf_centralizer_eq_bot_of_center (V_le_K h h31) hZ
        · obtain ⟨m, hm, hpsl, -⟩ := c2
          rcases hm with rfl | rfl
          · have hp : IsPSL 3 2 1 (ModO2 L) := by
              rw [hL0]
              exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm hpsl
            have h1 := hcov hp
            rw [eq_bot_iff] at h1 ⊢
            rintro v ⟨hv, hvC⟩
            exact h1 ⟨hv, V_le_K h h31 hv, hvC⟩
          · exfalso
            rw [hcard, card_of_isPSL_four_two hpsl] at hdiv
            revert hdiv
            decide
      exact c48Case2_of_img h h31 hL hVK c2
    ·
      right; right; left
      obtain ⟨hspor, hblock⟩ := c3
      refine ⟨?_, ?_⟩
      · rcases hspor with hs | hs
        · exact Or.inl (IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs)
        · exact Or.inr (IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs)
      · rw [hL0]
        exact isAltBlockType_of_img h h31 hblock
    ·
      right; right; right; left
      obtain ⟨hM23, hexc⟩ := c4
      have hZ' := hshape 2520 (Or.inl rfl) (card_modO2_of_isExcA7Block hexc)
      refine ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hM23, ?_⟩
      rw [hL0]
      exact isExcA7Block_of_img h h31 hexc
    ·
      right; right; right; right; left
      obtain ⟨hspor, hhat⟩ := c5
      have hZ' := hshape 1080 (Or.inr (Or.inl rfl)) (card_modO2_of_isHatA6Block hhat)
      refine ⟨?_, ?_⟩
      · rcases hspor with hs | hs
        · exact Or.inl (IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hs)
        · exact Or.inr (IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hs)
      · rw [hL0]
        exact isHatA6Block_of_img h h31 hZ' hhat
    ·
      right; right; right; right; right; left
      have hZ' : Subgroup.center ↥K = ⊥ := by
        rcases hZ with hZ | ⟨hdiv, -⟩
        · exact hZ
        · exfalso
          obtain ⟨-, -, ⟨h24, -⟩ | ⟨h5, -⟩⟩ := c6
          · have h23 := dvd_card_of_isSporadic_m24 h24
            rw [← hcard] at h23
            rcases hdiv with hd | hd | hd | hd <;> have := h23.trans hd <;> revert this <;> decide
          · rw [hcard, card_of_isPSL_five_two h5] at hdiv
            revert hdiv
            decide
      exact c48Case6_of_img h hK h31 hL hZ' c6
    ·
      right; right; right; right; right; right
      obtain ⟨hRu, hG2⟩ := c7
      refine ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hRu, ?_⟩
      rw [hL0]
      exact isG2Block_of_img h h31 hG2
  ·
    intro m k hm hpsl hsum
    have hm2 : 2 ≤ m := by omega
    obtain ⟨-, hsum'⟩ := sum_img h h31 hL hm2 hsum
    have hpsl' : IsPSL m 2 1 (ModO2 (img (sporN H K) (conjClosure L M))) := by
      rw [hL0] at hpsl
      exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31) hpsl
    exact hbound m k hm hpsl' hsum'

omit [Finite G] in
theorem isSporadic_quot_of_center {K : Subgroup G} {s : TauCeti.SporadicName}
    (hs : IsSporadic s ↥K) (hZ : Subgroup.center ↥K = ⊥) :
    IsSporadic s (↥K ⧸ Subgroup.center ↥K) :=
  IsSporadic.of_mulEquiv ((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))) hs

theorem c48SporStep_of
    (h22 : ASC22One G)
    (hInsp : InspC31Sporadic) (hCov : C48SporCoverFact G) : C48SporStep G := by
  intro H R M L V K h hK h31 hcase
  have hZ2 := isPGroup_center_of h31.2.2.2.2.1
  have hcover : (C31Case3 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case9 H R M L V K) →
      Subgroup.center ↥K = ⊥ ∨
      ((Nat.card (ModO2 (conjClosure L M)) ∣ 60 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 360 ∨
          Nat.card (ModO2 (conjClosure L M)) ∣ 168 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 6048) ∧
        (IsPSL 3 2 1 (ModO2 L) → V ⊓ centerOf K = ⊥)) := fun hc =>
    Or.inr ⟨card_modO2_dvd_of_c31Case379 h31.basic hc, hCov H R M L V K h hK h31 hc⟩
  rcases hcase with c3 | c4 | c5 | c6 | c7 | c8 | c9
  · exact c48SporStep_core h hK h31.basic h31.1 (hInsp .M22 (by simp)) (fun h => nomatch h) c3.1
      (hcover (Or.inl c3))
  · obtain ⟨e⟩ := c4.1
    have hZ := center_eq_bot_m23 e hZ2
    exact c48SporStep_core h hK h31.basic h31.1 (hInsp .M23 (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c4.1 hZ) (Or.inl hZ)
  · obtain ⟨e⟩ := c5.1
    have hZ := center_eq_bot_m24 e hZ2
    exact c48SporStep_core h hK h31.basic h31.1 (hInsp .M24 (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c5.1 hZ) (Or.inl hZ)
  · have hZ := center_eq_bot_j4 c6.1 hK.2.2
    exact c48SporStep_core h hK h31.basic h31.1 (hInsp .J4 (by simp))
      (fun _ => C31SporJ.normalizer_img_le_of_j4 h22 h hK h31.basic c6.1)
      (isSporadic_quot_of_center c6.1 hZ) (Or.inl hZ)
  · exact c48SporStep_core h hK h31.basic h31.1 (hInsp .HS (by simp)) (fun h => nomatch h) c7.1
      (hcover (Or.inr (Or.inl c7)))
  · have hZ := center_eq_bot_he c8.1 hK.2.2
    exact c48SporStep_core h hK h31.basic h31.1 (hInsp .He (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c8.1 hZ) (Or.inl hZ)
  · exact c48SporStep_core h hK h31.basic h31.1 (hInsp .Ru (by simp)) (fun h => nomatch h) c9.1
      (hcover (Or.inr (Or.inr c9)))

end CFSG.Quasithin.C48Spor
