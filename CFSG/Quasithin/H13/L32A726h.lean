module

public import CFSG.Quasithin.H13.L32A726g
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_conjugate_726 {M : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate M g ↔ g * y * g⁻¹ ∈ M := by
  rw [CFSG.conjugate, Subgroup.mem_map_equiv]
  simp

omit [Finite G] in
theorem conjugate_mul_726 (M : Subgroup G) (a b : G) :
    CFSG.conjugate M (a * b) = CFSG.conjugate (CFSG.conjugate M a) b := by
  ext y
  rw [mem_conjugate_726, mem_conjugate_726, mem_conjugate_726,
    show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group]

omit [Finite G] in
theorem conjugate_eq_self_iff_726 {M : Subgroup G} {g : G} :
    CFSG.conjugate M g = M ↔ g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff, SetLike.ext_iff]
  simp only [mem_conjugate_726]
  exact ⟨fun h y => (h y).symm, fun h y => (h y).symm⟩

omit [Finite G] in
theorem conjugate_injective_726 {A B : Subgroup G} {g : G}
    (h : CFSG.conjugate A g = CFSG.conjugate B g) : A = B := by
  ext y
  have h1 := SetLike.ext_iff.mp h (g⁻¹ * y * g)
  rwa [mem_conjugate_726, mem_conjugate_726,
    show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1

omit [Finite G] in
theorem conjugate_sup_726 (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g :=
  Subgroup.map_sup A B _

theorem mul_mem_normalizer_iff_726 {G0 M : Subgroup G}
    (hcard : Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2) {a b : G}
    (ha : a ∈ G0) (hb : b ∈ G0) :
    a * b ∈ Subgroup.normalizer (M : Set G) ↔
      (a ∈ Subgroup.normalizer (M : Set G) ↔ b ∈ Subgroup.normalizer (M : Set G)) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  set N := Subgroup.normalizer (M : Set G) with hN
  by_cases haN : a ∈ N <;> by_cases hbN : b ∈ N
  · exact iff_of_true (N.mul_mem haN hbN) (iff_of_true haN hbN)
  · refine iff_of_false (fun hab => hbN ?_) (fun h => hbN (h.mp haN))
    rw [show b = a⁻¹ * (a * b) by group]
    exact N.mul_mem (N.inv_mem haN) hab
  · refine iff_of_false (fun hab => haN ?_) (fun h => haN (h.mpr hbN))
    rw [show a = a * b * b⁻¹ by group]
    exact N.mul_mem hab (N.inv_mem hbN)
  ·
    refine iff_of_true ?_ (iff_of_false haN hbN)
    by_contra habN
    have h1 : CFSG.conjugate M b ≠ M := fun h => hbN (conjugate_eq_self_iff_726.mp h)
    have h2 : CFSG.conjugate M (a * b) ≠ M := fun h => habN (conjugate_eq_self_iff_726.mp h)
    have h3 : CFSG.conjugate M b ≠ CFSG.conjugate M (a * b) := by
      intro h
      rw [conjugate_mul_726] at h
      exact haN (conjugate_eq_self_iff_726.mp (conjugate_injective_726 h).symm)
    let f : Fin 3 → {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} :=
      ![⟨M, 1, G0.one_mem, (conjugate_eq_self_iff_726.mpr (Subgroup.one_mem _)).symm⟩,
        ⟨CFSG.conjugate M b, b, hb, rfl⟩, ⟨CFSG.conjugate M (a * b), a * b, G0.mul_mem ha hb, rfl⟩]
    have h1' := h1.symm
    have h2' := h2.symm
    have h3' := h3.symm
    have hf : Function.Injective f := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_fin] at this
    omega

theorem mem_normalizer_of_odd_726 {G0 M : Subgroup G}
    (hcard : Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2) {y : G}
    (hy : y ∈ G0) (hodd : Odd (orderOf y)) : y ∈ Subgroup.normalizer (M : Set G) := by
  by_contra hyN
  have h2 : y * y ∈ Subgroup.normalizer (M : Set G) :=
    (mul_mem_normalizer_iff_726 hcard hy hy).mpr (iff_of_false hyN hyN)
  have hmem : y ∈ Subgroup.zpowers (y ^ 2) :=
    A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hodd)
  rw [pow_two] at hmem
  exact hyN ((Subgroup.zpowers_le.mpr h2) hmem)

theorem le_normalizer_of_perfect_726 {G0 M P : Subgroup G}
    (hcard : Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2)
    (hPG0 : P ≤ G0) (hP : ⁅P, P⁆ = P) : P ≤ Subgroup.normalizer (M : Set G) := by
  rw [← hP, Subgroup.commutator_le]
  intro a ha b hb
  have haG := hPG0 ha
  have hbG := hPG0 hb
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group,
    mul_mem_normalizer_iff_726 hcard (G0.mul_mem haG hbG) (G0.mul_mem (G0.inv_mem haG)
      (G0.inv_mem hbG)), mul_mem_normalizer_iff_726 hcard haG hbG,
    mul_mem_normalizer_iff_726 hcard (G0.inv_mem haG) (G0.inv_mem hbG),
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]

theorem conjugate_sup_eq_726 {G0 M : Subgroup G}
    (hcard : Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2) {g : G}
    (hg : g ∈ G0) (hgN : g ∉ Subgroup.normalizer (M : Set G)) {h : G} (hh : h ∈ G0) :
    CFSG.conjugate (CFSG.conjugate M g ⊔ M) h = CFSG.conjugate M g ⊔ M := by
  rw [conjugate_sup_726, ← conjugate_mul_726]
  by_cases hhN : h ∈ Subgroup.normalizer (M : Set G)
  ·
    have hx : g * h * g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
      rw [mul_mem_normalizer_iff_726 hcard (G0.mul_mem hg hh) (G0.inv_mem hg),
        mul_mem_normalizer_iff_726 hcard hg hh, Subgroup.inv_mem_iff]
      tauto
    have h1 : CFSG.conjugate M (g * h) = CFSG.conjugate M g := by
      rw [show g * h = g * h * g⁻¹ * g by group, conjugate_mul_726 M (g * h * g⁻¹) g,
        conjugate_eq_self_iff_726.mpr hx]
    rw [h1, conjugate_eq_self_iff_726.mpr hhN]
  ·
    have hx : h * g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
      rw [mul_mem_normalizer_iff_726 hcard hh (G0.inv_mem hg), Subgroup.inv_mem_iff]
      tauto
    have h1 : CFSG.conjugate M h = CFSG.conjugate M g := by
      rw [show h = h * g⁻¹ * g by group, conjugate_mul_726 M (h * g⁻¹) g,
        conjugate_eq_self_iff_726.mpr hx]
    have h2 : CFSG.conjugate M (g * h) = M := by
      rw [conjugate_eq_self_iff_726, mul_mem_normalizer_iff_726 hcard hg hh]
      tauto
    rw [h1, h2, sup_comm]

theorem exists_normal_of_not_three_dvd_726 {G0 M : Subgroup G}
    (hcard : Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2)
    (hM : M ∈ cComp G0) (h3 : ¬ 3 ∣ Nat.card M) :
    ∃ I : Subgroup G, M ≤ I ∧ I ≤ G0 ∧ G0 ≤ Subgroup.normalizer (I : Set G) ∧
      ¬ 3 ∣ Nat.card I := by
  have hMG0 := le_of_mem_cComp hM
  by_cases hN : G0 ≤ Subgroup.normalizer (M : Set G)
  · exact ⟨M, le_rfl, hMG0, hN, h3⟩
  obtain ⟨g, hg, hgN⟩ : ∃ g ∈ G0, g ∉ Subgroup.normalizer (M : Set G) := by
    by_contra hall
    push Not at hall
    exact hN hall
  have hM'c : CFSG.conjugate M g ∈ cComp G0 :=
    C2Nine.conjByElt_mem_cComp hM (Subgroup.le_normalizer (G0.inv_mem hg))
  have hM'G0 := le_of_mem_cComp hM'c
  have hM'N : CFSG.conjugate M g ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_of_perfect_726 hcard hM'G0 (perfect_of_mem_cComp hM'c)
  have hcardM' : Nat.card (CFSG.conjugate M g) = Nat.card M :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  refine ⟨CFSG.conjugate M g ⊔ M, le_sup_right, sup_le hM'G0 hMG0, fun h hh => ?_, fun h3' => ?_⟩
  · exact conjugate_eq_self_iff_726.mp (conjugate_sup_eq_726 hcard hg hgN hh)
  · have e := card_sup_mul_726 hM'N
    rw [hcardM'] at e
    have h3'' : 3 ∣ Nat.card M * Nat.card M := e ▸ h3'.mul_right _
    exact h3 (((Nat.Prime.dvd_mul Nat.prime_three).mp h3'').elim id id)

theorem not_mem_pCoreOf_726 {X : Subgroup G} {x : G} (hx3 : orderOf x = 3) :
    x ∉ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hx
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 X) ⟨x, hx⟩
  have h1 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : 3 ∣ 2 ^ n := hx3 ▸ orderOf_dvd_of_pow_eq_one h1
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)

theorem exists_mem_cComp_726 {X : Subgroup G} (hX : ¬ Group.IsSolvable ↥X) :
    ∃ M : Subgroup G, M ∈ cComp X := by
  have hne : perfectCore X ≠ ⊥ := fun h => hX ((isSolvable_iff_perfectCore_eq_bot X).mpr h)
  obtain ⟨M, hM⟩ := (Set.toFinite
    {K : Subgroup G | K ≠ ⊥ ∧ perfectCore K = K ∧ IsSubnormal K X}).exists_minimal
    ⟨perfectCore X, hne, perfectCore_eq_self_of_perfect (perfectCore_perfect X),
      A3.subnormal_perfectCore (IsSubnormal.refl X)⟩
  exact ⟨M, mem_cComp_iff_minimal.mpr hM⟩

theorem eq_of_mem_cComp_726 {G0 : Subgroup G} (hodd : OddCoreModTwoTrivial G0)
    {M M' : Subgroup G} (hM : M ∈ cComp G0) (hM' : M' ∈ cComp G0) {x : G} (hx3 : orderOf x = 3)
    (hxM : x ∈ M) (hxM' : x ∈ M') : M = M' := by
  have key : ∀ {A B : Subgroup G}, A ∈ cComp G0 → B ∈ cComp G0 → x ∈ A → x ∈ B → A ≤ B := by
    intro A B hA hB hxA hxB
    by_contra hAB
    have hsub : IsSubnormal (B ⊓ A) A :=
      A3.subnormal_inf_right (subnormal_of_mem_cComp hB) (le_of_mem_cComp hA)
    have hlt : B ⊓ A < A := lt_of_le_of_ne inf_le_right fun h => hAB (by
      rw [← h]
      exact inf_le_left)
    have h1 := le_solvRad_of_subnormal_lt hA hsub hlt
    rw [solvRad_eq_pCoreOf_of_mem_cComp hodd hA] at h1
    exact not_mem_pCoreOf_726 hx3 (h1 ⟨hxB, hxA⟩)
  exact le_antisymm (key hM hM' hxM hxM') (key hM' hM hxM' hxM)

section Ctx

variable {T L V H D : Subgroup G}

theorem isSolvable_h_726 (hc : Ctx726 G T L V H D) : Group.IsSolvable H := by
  obtain ⟨a, ha⟩ := exists_card_h_726 hc
  have := Fintype.ofFinite ↥H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a)
    (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, ha]; norm_num)

theorem not_le_h_of_mem_cComp_726 (hc : Ctx726 G T L V H D) {G0 M : Subgroup G}
    (hM : M ∈ cComp G0) : ¬ M ≤ H := fun h => by
  have := isSolvable_h_726 hc
  exact not_isSolvable_of_mem_cComp hM
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h))

theorem card_conj_le_two_726 (h121 : Id2519.Prop121Three) (hc : Ctx726 G T L V H D)
    {G0 : Subgroup G} (hG0 : pCoreOf 2 G0 ≠ ⊥) {M : Subgroup G} (hM : M ∈ cComp G0) :
    Nat.card {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} ≤ 2 := by
  have := hc.setting.hyp.fsu.simple
  rcases h121 G hc.setting.hyp.fsu.simple hc.setting.hyp.fsu.nonabelian
    (QuasithinUnique.qtkeCore_of_cat hc.setting.hyp.fsu.nonabelian hc.setting.hyp.fsu.qtke)
    G0 hG0 M hM with hN | ⟨h2, -⟩
  · have : Subsingleton {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h} := ⟨fun a b => by
      obtain ⟨_, h, hh, rfl⟩ := a
      obtain ⟨_, h', hh', rfl⟩ := b
      rw [Subtype.mk.injEq, conjugate_eq_self_iff_726.mpr (hN hh),
        conjugate_eq_self_iff_726.mpr (hN hh')]⟩
    rw [Nat.card_of_subsingleton (⟨M, 1, Subgroup.one_mem _,
      (conjugate_eq_self_iff_726.mpr (Subgroup.one_mem _)).symm⟩ :
        {K : Subgroup G // ∃ h ∈ G0, K = CFSG.conjugate M h})]
    norm_num
  · omega

theorem three_dvd_card_of_mem_cComp_726 (hC129 : ASC129Statement G)
    (h121 : Id2519.Prop121Three) (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t)
    {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G))
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) (hchar : CharTwo G0)
    {M : Subgroup G} (hM : M ∈ cComp G0) : 3 ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h3
  have hcard := card_conj_le_two_726 h121 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0) hM
  obtain ⟨I, hMI, hIG0, hG0I, h3I⟩ := exists_normal_of_not_three_dvd_726 hcard hM h3
  have hIc : CharTwo I := CharTwo.of_normal hchar hIG0
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hIG0).mpr hG0I)
  have hQG0 : pCoreOf 2 H ≤ G0 := (hQ.trans (td_le_hd_726 hc d)).trans hHdG0
  have hXc := charTwo_sup_726 hIc (pCoreOf_isPGroup 2 H) (hQG0.trans hG0I)
  have hIHd := le_hd_of_not_three_dvd_726 hC129 hc hdD hdV hd2 htT htd hHdG0 hG0 hQ hIG0 hG0I
    h3I hXc
  exact not_le_h_of_mem_cComp_726 hc hM (hMI.trans (hIHd.trans inf_le_left))

theorem k_le_normalizer_of_mem_cComp_726 (h121 : Id2519.Prop121Three)
    (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1)
    {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) {M : Subgroup G} (hM : M ∈ cComp G0) :
    oTwoUpper H ≤ Subgroup.normalizer (M : Set G) := by
  have hcard := card_conj_le_two_726 h121 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0) hM
  have hKG0 : oTwoUpper H ≤ G0 := (k_le_hd_726 hc hdD).trans hHdG0
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  exact mem_normalizer_of_odd_726 hcard (hKG0 (mem_oTwoUpper_of_odd hy.1 hy.2)) hy.2

theorem mem_of_mem_cComp_of_three_dvd_726 (h121 : Id2519.Prop121Three)
    (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1)
    {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) {x : G} {Y E₁ E₂ : Subgroup G}
    (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂) {M : Subgroup G}
    (hM : M ∈ cComp G0) (h3 : 3 ∣ Nat.card M) : x ∈ M := by
  have hKN := k_le_normalizer_of_mem_cComp_726 h121 hc hdD hdV hd2 hHdG0 hG0 hM
  have hKG0 : oTwoUpper H ≤ G0 := (k_le_hd_726 hc hdD).trans hHdG0
  obtain ⟨W, -, -, -, hxW, -⟩ := iLemma_726
    (pRank_three_le_726 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0))
    (hX.y_le.trans hKG0) hX.y_pgroup hX.e₁_le hX.e₂_le hX.e₁_elem hX.e₂_elem hX.e₁_card
    hX.e₂_card hX.x_order hX.inf_le (le_of_mem_cComp hM) (hX.y_le.trans hKN) h3
  exact hxW.2

theorem exists_cComp_726 (hC129 : ASC129Statement G) (h121 : Id2519.Prop121Three)
    (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1)
    {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) (hG0H : ¬ G0 ≤ H)
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) (hchar : CharTwo G0)
    {x : G} {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂) :
    OddCoreModTwoTrivial G0 ∧ ∃ L₀ ∈ cComp G0, x ∈ L₀ ∧
      G0 ≤ Subgroup.normalizer (L₀ : Set G) := by
  have hO : ∀ N : Subgroup G, N ≤ G0 → G0 ≤ Subgroup.normalizer (N : Set G) →
      Odd (Nat.card N) → N = ⊥ := fun N hNG0 hG0N hodd => by
    by_contra hne
    exact Ch1.not_charTwo_of_normal_odd hNG0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNG0).mpr hG0N) hodd hne hchar
  have hodd := oddCoreModTwoTrivial_726 hC129 hc hdD hdV hd2 htT htd hHdG0 hG0 hG0H hQ hO
  refine ⟨hodd, ?_⟩
  have hns : ¬ Group.IsSolvable G0 := by
    intro hs
    have h1 := solvRad_le_pCoreOf_of_oddCore hodd
    rw [(solvRad_eq_self_iff G0).mpr hs] at h1
    exact hG0H (h1.trans ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0)).trans
      (inf_le_left.trans (t_le_h_726 hc))))
  obtain ⟨L₀, hL₀⟩ := exists_mem_cComp_726 hns
  have hmem := fun {M : Subgroup G} (hM : M ∈ cComp G0) =>
    mem_of_mem_cComp_of_three_dvd_726 h121 hc hdD hdV hd2 hHdG0 hG0 hX hM
      (three_dvd_card_of_mem_cComp_726 hC129 h121 hc hdD hdV hd2 htT htd hHdG0 hG0 hQ hchar hM)
  refine ⟨L₀, hL₀, hmem hL₀, fun h hh => ?_⟩
  have hc' : CFSG.conjugate L₀ h ∈ cComp G0 :=
    C2Nine.conjByElt_mem_cComp hL₀ (Subgroup.le_normalizer (G0.inv_mem hh))
  exact conjugate_eq_self_iff_726.mp
    (eq_of_mem_cComp_726 hodd hc' hL₀ hX.x_order (hmem hc') (hmem hL₀))

end Ctx

end CFSG.Quasithin.H13.L32A
