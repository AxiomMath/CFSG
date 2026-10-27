module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31d
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs9
public import CFSG.Quasithin.Background.SmithC27RTypeRank2
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 Equiv
  CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_inf_centralizer_eq_center {Y : Type*} [Group Y] (X : Subgroup Y) :
    Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set Y)) = Nat.card ↥(Subgroup.center ↥X) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 z.2.2 g g.2)⟩
      invFun := fun z => ⟨z.1.1, z.1.2, Subgroup.mem_centralizer_iff.2 fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩)⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }


theorem isPSL_statedProj_card_four_P31 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    IsPSL 3 2 2 (StatedProj (StatedSL 3 F)) := by
  letI := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  have h1 := SmithC27.isPSL_statedSL_three (F := F) (n := 2) (by norm_num) hF'
  exact IsPSL.of_mulEquiv
    ((SmithC27.quotCenterCongr (specialLinearGroupEquivStatedSL 3 F).symm).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 F)) h1

theorem not_comm_of_simple_card {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hc : ¬ (Nat.card X).Prime) : ¬ ∀ a b : X, a * b = b * a := by
  intro h
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := h }
  exact hc (IsSimpleGroup.prime_card (α := X))


section CaseOne

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]
  {H K : Subgroup G}

theorem case1_of (hLie : L34LieFacts12631) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h1229 : Lemma12_6_29) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hHK : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K)
    (hF : ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 4 ∧
      (Nonempty (↥(star H K) ≃* PSL3Model F') ∨
        Nonempty (↥(star H K) ≃* ↥(StatedSL 3 F')))) :
    Case1 T L H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ h918.K₀_normal
  have hHeq : H = K ⊔ (Li L F.V1 ⊔ T) := by
    have := hHK.2.2
    rwa [hK₀] at this
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h.L₁T_le_H
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans hL1TH
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hsylT
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hQR : pCoreOf 2 H ≤ Ri T L F.V1 :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hL1TH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hL1TM : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (L : Set G) ⊓ H :=
    le_inf (sup_le (F126.L1_le_L.trans Subgroup.le_normalizer) hH.hyp.normalizes) hL1TH
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    hQT.trans hH.hyp.normalizes
  set Ks := star H K with hKs
  set Ts := star H T with hTs
  set Ms := star H (Subgroup.normalizer (L : Set G) ⊓ H) with hMs
  set Bs := star H (Li L F.V1 ⊔ T) with hBs
  set Ls := star H (Li L F.V1) with hLs
  set Rs := star H (Ri T L F.V1) with hRs
  haveI hKsn : Ks.Normal := normal_star hKn
  have hsup : Ks ⊔ Bs = ⊤ := by
    rw [hKs, hBs, ← star_sup hKH hL1TH, ← hHeq, star_self]
  have h27 : ¬ 27 ∣ Nat.card Ms := fun hd =>
    not_27_dvd_card_normalizer h1222 h1228 F hH
      (hd.trans ((Dvd.intro _ (F126.card_star
        (inf_le_right : Subgroup.normalizer (L : Set G) ⊓ H ≤ H))).trans
        (Subgroup.card_dvd_of_le inf_le_left)))
  have h9 : 9 ∣ Nat.card Ls := F126.nine_dvd_card_star_L1 F hH h
  have hcop6 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → Nat.Coprime p 6 := by
    intro p hp hp2 hp3
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h6
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h6) with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h2)
  have hL23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Ls → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_contra hne
    push Not at hne
    have h1 := coprime_card_L1T h1222 F hH h.T_normalizes_V₁ (hcop6 p hp hne.1 hne.2)
    have h2 : Nat.card Ls ∣ Nat.card (Li L F.V1) := Dvd.intro _ (F126.card_star hL1H)
    have h3 : Nat.card (Li L F.V1) ∣ Nat.card ↥(Li L F.V1 ⊔ T) :=
      Subgroup.card_dvd_of_le le_sup_left
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 (hpd.trans (h2.trans h3)))
  have hcop : ∀ (y : HStar H) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ Ks :=
    fun y n hy hc =>
      mem_star_of_coprime h1222 F hH h.T_normalizes_V₁ hKH hKn hL1TH hHeq hy hc
  have hm3 : ∀ A B C : Subgroup (HStar H), Nat.card A = 3 → Nat.card B = 3 → Nat.card C = 3 →
      A ≤ Subgroup.centralizer (B : Set (HStar H)) →
      A ≤ Subgroup.centralizer (C : Set (HStar H)) →
      B ≤ Subgroup.centralizer (C : Set (HStar H)) → A ⊓ B = ⊥ → (A ⊔ B) ⊓ C = ⊥ → False :=
    fun A B C hA hB hC hAB hAC hBC hi hi' =>
      false_of_three hH (pCoreOf_ne_bot h) hA hB hC hAB hAC hBC hi hi'
  have hsol : ∀ Z : Subgroup (HStar H), Ts ≤ Z → Group.IsSolvable ↥Z → Z ≤ Ms :=
    fun Z hTZ hZs => le_star_M h1229 F hH hZ hTH (pCoreOf_ne_bot h) hTZ hZs
  have hXM : ¬ Ks ≤ Ms := not_le_star_M hKH hQM hHK.2.1
  have hLn : Ms ≤ Subgroup.normalizer (Ls : Set (HStar H)) := by
    refine star_le_normalizer_star hL1H inf_le_right ?_
    intro g hg
    have hgV1 : g ∈ Subgroup.normalizer (F.V1 : Set G) := h.H_normalizes_V₁ hg.2
    have hgL : g ∈ Subgroup.normalizer (L : Set G) := hg.1
    have hgN : g ∈ Subgroup.normalizer
        ((Subgroup.normalizer (F.V1 : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgV1 hx) (Subgroup.inv_mem _ hgV1)
      · intro hx
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgV1) hx) hgV1
        simpa [mul_assoc] using this
    exact S126L19b.normalizer_le_normalizer_oTwoRes' _
      (S126L19b.normalizer_inf_le_inf _ _ ⟨hgL, hgN⟩)
  have hRn : Bs ≤ Subgroup.normalizer (Rs : Set (HStar H)) :=
    star_le_normalizer_star (hR1T.trans hTH) hL1TH (le_normalizer_pCoreOf 2 _)
  have hRmax : ∀ N : Subgroup (HStar H), N ≤ Bs →
      Bs ≤ Subgroup.normalizer (N : Set (HStar H)) → IsPGroup 2 N → N ≤ Rs := by
    intro N hNB hBN hNp
    set Npre := pre H N ⊓ (Li L F.V1 ⊔ T) with hNpre
    have hNpreN : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (Npre : Set G) :=
      (le_inf (le_normalizer_pre hL1TH hBN) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hNprep : IsPGroup 2 Npre := by
      intro x
      have hx : (x : G) ∈ pre H N := x.2.1
      obtain ⟨hxH, hxN⟩ := mem_pre.1 hx
      obtain ⟨k, hk⟩ := hNp ⟨QuotientGroup.mk ⟨x, hxH⟩, hxN⟩
      have hk' : (QuotientGroup.mk ⟨x, hxH⟩ : HStar H) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hxq : ((x : G) ^ 2 ^ k) ∈ pCoreOf 2 H := by
        have h1 : (QuotientGroup.mk ((⟨x, hxH⟩ : ↥H) ^ 2 ^ k) : HStar H) = 1 := by
          rw [QuotientGroup.mk_pow]; exact hk'
        exact F126.mkH_eq_one_iff.1 h1
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨(x : G) ^ 2 ^ k, hxq⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hNR : Npre ≤ Ri T L F.V1 := le_pCoreOf_of_le_normalizer 2 inf_le_right hNpreN hNprep
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hNB hx
    have hyL : (y : G) ∈ Li L F.V1 ⊔ T := hy
    have hyN : (y : G) ∈ Npre := ⟨mem_pre.2 ⟨y.2, hx⟩, hyL⟩
    exact mk_mem_star (hNR hyN)
  have hRidx : 4 ≤ Rs.relIndex Ts := by
    rw [hRs, hTs, relIndex_star hQR hR1T hTH]
    exact four_le_relIndex h1222 F hH
  have hperf : ⁅Ks, Ks⁆ = Ks := perfect_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp)
  have hLB : Ls ≤ Bs := star_mono le_sup_left
  have hTB : Ts ≤ Bs := star_mono le_sup_right
  have hBM : Bs ≤ Ms := star_mono hL1TM
  have hRT : Rs ≤ Ts := star_mono hR1T
  have hO2 : ∀ N : Subgroup (HStar H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hn hp => eq_bot_of_isPGroup hn hp
  obtain ⟨F', hFld, hFin, hF4, hiso⟩ := hF
  rcases hiso with hL | hS
  ·
    obtain ⟨eL⟩ := hL
    have hfacts : L34Facts12631 Ks := (hLie F' hF4 (HStar H) Ks).1 ⟨eL⟩
    have hPSL : IsPSL 3 2 2 ↥Ks :=
      IsPSL.of_mulEquiv eL.symm (isPSL_statedProj_card_four_P31 hF4)
    have hsimple : IsSimpleGroup ↥Ks := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hPSL).2
    have hXc : Nat.card ↥Ks = 20160 := by
      have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F') (n := 3)
        (by norm_num)
      rw [Nat.card_congr eL.toEquiv, h1, hF4]
      decide
    have hXn : ¬ ∀ a b : ↥Ks, a * b = b * a :=
      not_comm_of_simple_card (by rw [hXc]; norm_num)
    obtain ⟨hKM, ⟨φ⟩, hMsE⟩ := case1L_abs Ks Ts Ms Bs Ls Rs hsimple hXn hperf hXc hfacts hsylTs
      hO2 hsol hXM hTB hBM hLB hLn hsup h27 h9 hL23 hcop hm3 hRT hRmax hRidx
    exact ⟨hK₀, Or.inl ⟨F', hFld, hFin, hF4, ⟨eL⟩, ⟨φ.trans (MulAut.congr eL)⟩⟩, hMsE⟩
  ·
    obtain ⟨eS⟩ := hS
    have hfacts : SL34Facts12631 Ks := (hLie F' hF4 (HStar H) Ks).2 ⟨eS⟩
    have hXc : Nat.card ↥Ks = 60480 := by
      have h1 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F') (n := 3)
        (by norm_num)
      rw [hF4, Nat.card_congr (specialLinearGroupEquivStatedSL 3 F').toEquiv,
        ← Nat.card_congr eS.toEquiv] at h1
      rw [h1]
      decide
    have hZc : Nat.card ↥(Ks ⊓ Subgroup.centralizer (Ks : Set (HStar H))) = 3 := by
      rw [card_inf_centralizer_eq_center, Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (K := F')
        (by simp [hF4])
    obtain ⟨hKM, hidx, hsq, hMsE⟩ := case1S_abs Ks Ts Ms Bs Ls Rs hperf hXc hfacts hZc hsylTs
      hO2 hsol hXM hTB hBM hLB hLn hsup h27 h9 hL23 hcop hRT hRmax hRidx
    exact ⟨hK₀, Or.inr ⟨F', hFld, hFin, hF4, ⟨eS⟩, hidx, hsq⟩, hMsE⟩

end CaseOne

end CFSG.Quasithin.H13.S126P31
