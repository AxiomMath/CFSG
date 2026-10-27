module

public import CFSG.Quasithin.Vol2.E2SevenNS
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

structure StarCase2 (M H T K : Subgroup G) : Prop where
  sup : star M H K ⊔ star M H T = ⊤
  normal : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer (star M H K : Set (StarQuot M H))
  cent : Subgroup.centralizer (star M H K : Set (StarQuot M H)) = ⊥
  simple : IsSimpleGroup ↥(star M H K)
  nonab : ∃ a b : ↥(star M H K), a * b ≠ b * a
  sylow : IsSylowTwoOf (star M H T ⊓ star M H K) (star M H K)

theorem starCase2_of (h : Hyp28 H T M V) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥(star M H K)) : StarCase2 M H T K := by
  have := E2P.finite_starQuot M H
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hKT : star M H K ⊔ star M H T = ⊤ := by
    rw [← star_sup hKH hTH, ← hHK, E2P.star_top]
  have hTN : star M H T ≤ Subgroup.normalizer (star M H K : Set (StarQuot M H)) := by
    rintro _ ⟨⟨t, htH⟩, ht, rfl⟩
    exact starMap_mem_normalizer htH (hTK (Subgroup.mem_subgroupOf.mp ht))
  have hKN : (⊤ : Subgroup (StarQuot M H)) ≤
      Subgroup.normalizer (star M H K : Set (StarQuot M H)) := by
    rw [← hKT]
    exact sup_le Subgroup.le_normalizer hTN
  have hKn : (star M H K).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKN)
  have hnab : ∃ a b : ↥(star M H K), a * b ≠ b * a := by
    have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
    have : Nontrivial ↥(star M H K) := hs.toNontrivial
    exact nonabelian_of_perfect_of_surjective
      (((E2P.starMap M H).subgroupMap (K.subgroupOf H)).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (((E2P.starMap M H).subgroupMap_surjective _).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  exact ⟨hKT, hKN, centralizer_eq_bot_of_simple hmpY (E2P.kerIn_star M H) hKn hs hnab hKT,
    hs, hnab, A4.isSylowTwoOf_inf_normal hmpY.isSylow le_top hKN⟩

theorem exists_isInIHTVC_of_l3 (hKG2 : KGBenderSubL2) (hKG6 : KGL3Even) (h : Hyp28 H T M V)
    (hJ : kerIn M H = ⊥) {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn1 : 1 ≤ n)
    (hL3 : IsPSL 3 2 n ↥(star M H K))
    (hD : IsDiagramNontrivial (star M H T) (star M H K) (star M H (T ⊓ K)))
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K)))
    (hnstar : E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) (hSQs : SQTKGroup (StarQuot M H))
    (hV4 : 4 ≤ Nat.card V) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hY28 := h.star (sqtkGroup_top hSQs)
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY : kerIn (star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have hs : IsSimpleGroup ↥(star M H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n hL3).2
  have hC := starCase2_of h hKc hHK hTK hs
  have hMK := star_inf_eq_of_isBorelIn h.minParabolic hC.normal hB
  have hTK' : star M H (T ⊓ K) = star M H T ⊓ star M H K :=
    E2P.star_inf_T h.minParabolic.isSylow (hKc.2.2.1) hKH
  rw [hTK'] at hD
  have hV4s : 4 ≤ Nat.card ↥(star M H V) := by
    rw [card_star_of_kerIn_eq_bot hJ h.le_H]
    exact hV4
  obtain ⟨hn2, L, hLK, hL2, hSL, hVSL, hVZL, hML⟩ := hKG6 (StarQuot M H) ⊤ (star M H T)
    (star M H M) (star M H K) (star M H V) n hmpY hJY le_top hC.normal
    (by rw [top_inf_eq]; exact hC.cent) hC.sup hn1 hL3 hD hMK hY28.le_pCoreOf hY28.elem
    hY28.normal_T hV4s
  have hsL : IsSimpleGroup ↥L := isSimpleGroup_of_psl_or_sz (Or.inl hL2)
  have hnabL := nonabelian_of_psl_or_sz (by omega) (Or.inl hL2)
  obtain ⟨g₀, hg₀L, hg₀N⟩ := exists_not_mem_normalizer_of_simple hsL hnabL hSL
    (fun hb => hY28.ne_bot (le_bot_iff.mp (hb ▸ hVSL)))
  obtain ⟨g, hgL, hgN, hsyl, ⟨k, hk2, hkn, hYk⟩, hBor, ⟨h₀, hh₀, hI₀⟩⟩ :=
    exists_member_of_bender (⟨hn2, Or.inl hL2⟩ : IsBenderOf n ↥L) hSL hVSL hV4s hg₀L hg₀N
      fun g' hg'L hg'N => hKG2 (StarQuot M H) L (star M H T ⊓ L) (star M H V) n g' hn2 hL2 hSL
        hVSL hVZL hY28.elem hV4s hg'L hg'N
  set I₀ := star M H V ⊔ conjSub g (star M H V) with hI₀def
  have hVL : star M H V ≤ L := hVSL.trans inf_le_right
  have hI₀L : I₀ ≤ L := sup_le hVL (by
    intro w hw
    rw [mem_conjSub] at hw
    have := L.mul_mem (L.mul_mem hgL (hVL hw)) (L.inv_mem hgL)
    simpa [mul_assoc] using this)
  have hTI : star M H T ⊓ I₀ = (star M H T ⊓ L) ⊓ I₀ := by
    rw [inf_assoc, inf_eq_right.mpr hI₀L]
  have hmem : ASInputs.IsInIHTVC ⊤ (star M H T) (star M H M) (star M H V) I₀ := by
    refine isInIHTVC_of_simple le_top hh₀ hI₀ (le_inf hY28.le_T le_sup_left) hY28.ne_bot
      (by rw [hTI]; exact hsyl) (by omega) hYk ?_ ?_
    · rw [hTI, ← hBor, ← hML, inf_assoc, inf_eq_right.mpr hI₀L]
    · obtain ⟨m, rfl⟩ := hkn
      exact ⟨m, by rw [hnstar]⟩
  exact exists_isInIHTVC_of_star h (nParam_star_of_kerIn_eq_bot hJ) hmem

noncomputable def equivStarOfKerInEqBot (hJ : kerIn M H = ⊥) {K : Subgroup G} (hKH : K ≤ H) :
    ↥K ≃* ↥(star M H K) :=
  (Subgroup.subgroupOfEquivOfLe hKH).symm.trans
    ((K.subgroupOf H).equivMapOfInjective (E2P.starMap M H) (by
      rw [← MonoidHom.ker_eq_bot_iff, E2P.ker_starMap, hJ, Subgroup.bot_subgroupOf]))

theorem false_of_l2odd (hKG4 : KGL2Odd) (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : e = 1 ∨ e = 2) (hpe : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7)
    (hK : IsPSL 2 p e ↥(star M H K))
    (hMK : star M H (M ⊓ K) = star M H K ⊓ Subgroup.centralizer
      ((star M H (T ⊓ K) ⊓ Subgroup.centralizer (star M H (T ⊓ K) : Set (StarQuot M H)) :
        Subgroup (StarQuot M H)) : Set (StarQuot M H)))
    (haut : 8 < autCard (star M H T) (star M H K)) (hSQs : SQTKGroup (StarQuot M H))
    (hV4 : 4 ≤ Nat.card V) : False := by
  have := E2P.finite_starQuot M H
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hY28 := h.star (sqtkGroup_top hSQs)
  have hs : IsSimpleGroup ↥(star M H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p e hK).2
  have hC := starCase2_of h hKc hHK hTK hs
  rw [E2P.star_inf_M, E2P.star_inf_T h.minParabolic.isSylow hKc.2.2.1 hKH] at hMK
  have h2 := hKG4 (StarQuot M H) ⊤ (star M H T) (star M H M) (star M H K) (star M H V) p e
    (E2P.minParabolic_star h.minParabolic) (E2P.kerIn_star M H) le_top hC.normal
    (by rw [top_inf_eq]; exact hC.cent) hC.sup hp hp3 he hpe hK hMK haut hY28.le_pCoreOf
    hY28.elem hY28.normal_T
  rw [card_star_of_kerIn_eq_bot hJ h.le_H] at h2
  omega

theorem oTwoUpper_eq_of_case2 (h : Hyp28 H T M V) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G)) : oTwoUpper H = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  refine le_antisymm (oTwoUpper_le_of_pow_mem fun x hx => ?_) (B1Red.perfect_le_oTwoUpper' hKH hKp)
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTK
  have hx' : x ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [← hHK]; exact hx
  rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right T K hTN] at hx'
  obtain ⟨t, ht, k, hk, rfl⟩ := hx'
  obtain ⟨m, hm⟩ := h.minParabolic.isSylow.2.1 ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine ⟨m, ?_⟩
  have key : ∀ j : ℕ, ∃ kj ∈ K, (t * k) ^ j = t ^ j * kj := by
    intro j
    induction j with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨kj, hkj, hkj'⟩ := ih
      refine ⟨(t⁻¹ * kj * t) * k, K.mul_mem ?_ hk, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) kj).mp hkj
        simpa [mul_assoc] using this
      · rw [pow_succ, hkj', pow_succ]
        group
  obtain ⟨kj, hkj, hkj'⟩ := key (2 ^ m)
  rw [hkj', htm, one_mul]
  exact hkj

theorem isL33Exception_of_l3eps (hKG5 : KGL3Eps) (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥(star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(star M H K) ∧ InducesOuter (star M H T) (star M H K)))
    (hMK : star M H (M ⊓ K) = star M H K ⊓ Subgroup.centralizer
      ((star M H (T ⊓ K) ⊓ Subgroup.centralizer (star M H (T ⊓ K) : Set (StarQuot M H)) :
        Subgroup (StarQuot M H)) : Set (StarQuot M H)))
    (hSQs : SQTKGroup (StarQuot M H)) (hV4 : 4 ≤ Nat.card V) : ASInputs.IsL33Exception H V := by
  have := E2P.finite_starQuot M H
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hY28 := h.star (sqtkGroup_top hSQs)
  have hs : IsSimpleGroup ↥(star M H K) := by
    rcases hK with ⟨-, hK⟩ | ⟨-, hK, -⟩
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 p 1 hK).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 p 1 hK).2
  have hC := starCase2_of h hKc hHK hTK hs
  rw [E2P.star_inf_M, E2P.star_inf_T h.minParabolic.isSylow hKc.2.2.1 hKH] at hMK
  have hV4s : 4 ≤ Nat.card ↥(star M H V) := by
    rw [card_star_of_kerIn_eq_bot hJ h.le_H]
    exact hV4
  obtain ⟨rfl, hVK⟩ := hKG5 (StarQuot M H) ⊤ (star M H T) (star M H M) (star M H K) (star M H V) p
    (E2P.minParabolic_star h.minParabolic) (E2P.kerIn_star M H) le_top hC.normal
    (by rw [top_inf_eq]; exact hC.cent) hC.sup hp hp2 hK hMK hY28.le_pCoreOf hY28.elem
    hY28.normal_T hV4s
  have hL : IsPSL 3 3 1 ↥(star M H K) := by
    rcases hK with ⟨h31, -⟩ | ⟨-, hK, -⟩
    · exact absurd h31 (by norm_num)
    · exact hK
  rw [ASInputs.IsL33Exception, oTwoUpper_eq_of_case2 h hKc hHK hTK]
  exact ⟨CFSG.SectionRank.statedClassicalModel_of_mulEquiv (equivStarOfKerInEqBot hJ hKH) hL,
    fun hle => hVK (star_mono hle)⟩

end E2

end CFSG.Quasithin
