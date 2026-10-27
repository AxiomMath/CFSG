module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Star
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2
public import CFSG.Quasithin.Background.C41PfF
public import CFSG.Quasithin.Background.PRankCommuteMod
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H

section Br

variable {G : Type} [Group G] [Finite G]

theorem isSimple_notSolvable_of_isPSL_cs5 {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (hX : IsPSL 2 2 n X) : IsSimpleGroup X ∧ ¬ Group.IsSolvable X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField X 2 2 n hX
  haveI : NeZero n := ⟨by omega⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hs, hns⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable hF
  refine ⟨e.isSimpleGroup_congr.mpr hs, fun hsol => hns ?_⟩
  haveI := hsol
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem center_eq_bot_of_isPSL_cs5 {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (hX : IsPSL 2 2 n X) : Subgroup.center X = ⊥ := by
  obtain ⟨hs, hns⟩ := isSimple_notSolvable_of_isPSL_cs5 hn hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    apply hns
    refine isSolvable_of_comm fun a b => ?_
    have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem not_isSolvable_star_cs5 {H I M : Subgroup G} (hIH : I ≤ H)
    (hker : kerIn (M ⊓ I) I = pCoreOf 2 I)
    (hns : ¬ Group.IsSolvable (E2.StarQuot (M ⊓ I) I)) :
    ¬ Group.IsSolvable ↥(E2.star (H ⊓ M) H I) := by
  intro hsol
  apply hns
  let π : ↥H →* E2.StarQuot (H ⊓ M) H := QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)
  let g : ↥I →* ↥(E2.star (H ⊓ M) H I) :=
    ((π.comp (Subgroup.inclusion hIH))).codRestrict (E2.star (H ⊓ M) H I) (fun a =>
      mem_star_cs5.mpr ⟨⟨a, hIH a.2⟩, a.2, rfl⟩)
  have hIJ : I ⊓ kerIn (H ⊓ M) H ≤ pCoreOf 2 I := by
    rw [← hker]
    intro x hx
    rw [mem_kerIn]
    intro b hb
    have hbH : b ∈ H := hIH hb
    have h1 : b * x * b⁻¹ ∈ kerIn (H ⊓ M) H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn (H ⊓ M) H hbH) x).mp hx.2
      exact this
    exact ⟨(kerIn_le h1).2, I.mul_mem (I.mul_mem hb hx.1) (I.inv_mem hb)⟩
  have hP2 : IsPGroup 2 (I ⊓ kerIn (H ⊓ M) H : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le hIJ
  haveI : Group.IsNilpotent ↥(I ⊓ kerIn (H ⊓ M) H) := hP2.isNilpotent
  haveI : Group.IsSolvable ↥(I ⊓ kerIn (H ⊓ M) H) := inferInstance
  haveI := hsol
  have hIsol : Group.IsSolvable ↥I := by
    refine solvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : I ⊓ kerIn (H ⊓ M) H ≤ I)) g ?_
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : π (Subgroup.inclusion hIH a) = 1 := by
      have := congrArg Subtype.val ha
      simpa [g] using this
    have h2 : (Subgroup.inclusion hIH a) ∈ (kerIn (H ⊓ M) H).subgroupOf H := by
      rw [← QuotientGroup.ker_mk' ((kerIn (H ⊓ M) H).subgroupOf H), MonoidHom.mem_ker]
      exact h1
    refine ⟨⟨(a : G), a.2, Subgroup.mem_subgroupOf.mp h2⟩, ?_⟩
    rfl
  exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)

theorem card_star_quot_le_cs5 {H I M : Subgroup G} (hIH : I ≤ H)
    (hker : kerIn (M ⊓ I) I = pCoreOf 2 I) :
    Nat.card (↥(E2.star (H ⊓ M) H I) ⧸
        (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) ≤
      Nat.card (E2.StarQuot (M ⊓ I) I) := by
  let π : ↥H →* E2.StarQuot (H ⊓ M) H := QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)
  have hmem : ∀ a : ↥I, π ⟨a, hIH a.2⟩ ∈ E2.star (H ⊓ M) H I := fun a =>
    mem_star_cs5.mpr ⟨⟨a, hIH a.2⟩, a.2, rfl⟩
  let f : ↥I → (↥(E2.star (H ⊓ M) H I) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) := fun a =>
    QuotientGroup.mk ⟨π ⟨a, hIH a.2⟩, hmem a⟩
  have hf : ∀ a b : ↥I, QuotientGroup.leftRel ((kerIn (M ⊓ I) I).subgroupOf I) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, hker] at hab
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show (π ⟨a, hIH a.2⟩)⁻¹ * π ⟨b, hIH b.2⟩ ∈ E2.star (H ⊓ M) H (pCoreOf 2 I)
    refine mem_star_cs5.mpr ⟨⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩, ?_, ?_⟩
    · simpa using hab
    · have e : (⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩ : ↥H) =
          (⟨a, hIH a.2⟩ : ↥H)⁻¹ * ⟨b, hIH b.2⟩ := rfl
      show (QuotientGroup.mk (⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩ : ↥H) :
        E2.StarQuot (H ⊓ M) H) = (π ⟨a, hIH a.2⟩)⁻¹ * π ⟨b, hIH b.2⟩
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
  let ψ : (↥I ⧸ (kerIn (M ⊓ I) I).subgroupOf I) → (↥(E2.star (H ⊓ M) H I) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) :=
    Quotient.lift f hf
  have hψ : Function.Surjective ψ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y₀ =>
      obtain ⟨a, ha, hay⟩ := mem_star_cs5.mp y₀.2
      refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
      show f ⟨a, ha⟩ = QuotientGroup.mk y₀
      exact congrArg QuotientGroup.mk (Subtype.ext hay)
  exact Nat.card_le_card_of_surjective ψ hψ

theorem l2_branch_cs5 {H T M K V : Subgroup G} {h : G} {n : ℕ}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hI : IsPSL 2 2 2 (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hn : 2 ≤ n) (hKs : IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K))
    (hBor : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    oTwoUpper H ≤ ch82I V h ⊔ kerIn (H ⊓ M) H := by
  have hTH : T ≤ H := hT.1
  have hVH : V ≤ H := hVT.trans hTH
  have hIH : ch82I V h ≤ H := ch82I_le_829 hVH hh
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hT2 : IsPGroup 2 T := hT.2.1
  haveI hXn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  have hYX : IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
    isPGroup_starQuot_quotient_cs5 hT2 hHK hTK
  have hO2 : ∀ N : Subgroup (E2.StarQuot (H ⊓ M) H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hN2 => by
      haveI := hN
      exact normal_twoGroup_starQuot_eq_bot_cs5 hT hTM N hN2
  have hC := eq_one_of_centralizes_normal_cs5 (center_eq_bot_of_isPSL_cs5 hn hKs) hYX hO2
  obtain ⟨S, hS, hB⟩ := hBor
  have hR := rankOneSyl_of_isPSL_two_cs5 hn hKs hS
  have hBsol : Group.IsSolvable ↥(E2.star (H ⊓ M) H K ⊓
      Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H))) := by
    have := C41Pf.isSolvable_of_isBorelIn
      (X := E2.star (H ⊓ M) H K) (B := E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) ⟨S, hS, hB⟩
    rwa [hB] at this
  set E := E2.star (H ⊓ M) H V with hEdef
  have hE : IsElemAbelian 2 E := isElemAbelian_star_cs5 hVH hVe
  have hEB : E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) ≤
      Subgroup.normalizer (E : Set (E2.StarQuot (H ⊓ M) H)) := by
    rw [← hB]
    exact star_le_normalizer_star_cs5 (inf_le_left.trans inf_le_left) hVH (inf_le_left.trans hP7)
  have hIstar : E2.star (H ⊓ M) H (ch82I V h) =
      E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E := by
    unfold ch82I
    obtain ⟨hconjH, hconj⟩ := star_conjSub_cs5 (M := H ⊓ M) hh hVH
    rw [star_sup_cs5 hVH hconjH, hconj]
  have hNnorm : ∀ i ∈ E2.star (H ⊓ M) H (ch82I V h),
      ∀ n ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)),
        i * n * i⁻¹ ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)) := by
    intro i hi n hn
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hi
    obtain ⟨p, hp, rfl⟩ := mem_star_cs5.mp hn
    refine mem_star_cs5.mpr ⟨a * p * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ch82I V h) ha) (p : G)).mp hp
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hN2 : IsPGroup 2 (E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))) :=
    isPGroup_star_cs5 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hQ60 : Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hI
  have hm := (card_star_quot_le_cs5 (H := H) (M := M) hIH hker).trans hQ60.le
  have hns := not_isSolvable_star_cs5 (H := H) hIH hker (not_isSolvable_of_isPSL_two_two_two_829 hI)
  obtain ⟨hZE, hne, hWX, hqq, hcardW⟩ := rk1_main_of_eq hR hC hYX hBsol hE hEB hIstar hNnorm hN2
    hm hns
  have hn2 : n = 2 := by
    by_contra hne2
    have h3 : 3 ≤ n := by omega
    have h8 : 8 ≤ 2 ^ n := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have := hqq.trans hcardW
    nlinarith
  subst hn2
  set hs : E2.StarQuot (H ⊓ M) H := QuotientGroup.mk (⟨h, hh⟩ : ↥H) with hsdef
  set W : Subgroup (E2.StarQuot (H ⊓ M) H) := centerSub S ⊔ B6.conjSub hs (centerSub S) with hW
  have h16 : 16 ≤ Nat.card ↥W := by
    have := hqq
    norm_num at this
    exact this
  have hX60 : Nat.card ↥(E2.star (H ⊓ M) H K) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hKs
  haveI hsimple : IsSimpleGroup ↥(E2.star (H ⊓ M) H K) :=
    (isSimple_notSolvable_of_isPSL_cs5 (le_refl 2) hKs).1
  have hWtop : W.subgroupOf (E2.star (H ⊓ M) H K) = ⊤ := by
    refine eq_top_of_simple_card_sixty_cs5 hX60 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv]
    exact h16
  have hKsW : E2.star (H ⊓ M) H K ≤ W := fun x hx => by
    have := hWtop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥(E2.star (H ⊓ M) H K))
    exact Subgroup.mem_subgroupOf.mp this
  have hWI : W ≤ E2.star (H ⊓ M) H (ch82I V h) := by
    rw [hIstar]
    exact sup_le (hZE.trans le_sup_left)
      (((B6.conjSub hs).monotone hZE).trans le_sup_right)
  have hKIJ : K ≤ ch82I V h ⊔ kerIn (H ⊓ M) H := by
    intro k hk
    have hkH : k ∈ H := hKH hk
    have h1 : (QuotientGroup.mk (⟨k, hkH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        E2.star (H ⊓ M) H (ch82I V h) :=
      hWI (hKsW (mem_star_cs5.mpr ⟨⟨k, hkH⟩, hk, rfl⟩))
    obtain ⟨a, ha, hak⟩ := mem_star_cs5.mp h1
    have h2 : a⁻¹ * (⟨k, hkH⟩ : ↥H) ∈ (kerIn (H ⊓ M) H).subgroupOf H :=
      QuotientGroup.eq.mp hak
    have h3 : (a : G)⁻¹ * k ∈ kerIn (H ⊓ M) H := by
      simpa [Subgroup.mem_subgroupOf] using h2
    have h4 : (a : G) * ((a : G)⁻¹ * k) = k := by group
    rw [← h4]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right h3)
  have hOK : oTwoUpper H ≤ K := by
    rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxH, hxo⟩
    have hx : x ∈ K ⊔ T := hHK ▸ hxH
    exact mem_of_mem_sup_of_pow_eq_one hTK hT2 hx hxo (pow_orderOf_eq_one x)
  exact hOK.trans hKIJ

end Br

end CFSG.Quasithin.H13
