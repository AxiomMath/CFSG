module

public import CFSG.Quasithin.Vol2.E2SevenSmall
public import CFSG.Quasithin.Vol2.E2SevenBender
public import CFSG.Quasithin.Vol2.E2NinePullback
public import CFSG.Quasithin.Vol2.E2NineStarSQTK
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.Quasithin.Background.E2TwoC
public import CFSG.Quasithin.Background.E1ElevenIso
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] noncomputable def starQuotEquivOfBot {M I : Subgroup G} (hker : kerIn (M ⊓ I) I = ⊥) :
    StarQuot (M ⊓ I) I ≃* ↥I :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [hker, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

omit [Finite G] in
theorem starQuotEquivOfBot_mk {M I : Subgroup G} (hker : kerIn (M ⊓ I) I = ⊥) (x : ↥I) :
    starQuotEquivOfBot hker (QuotientGroup.mk' _ x) = x := rfl

omit [Finite G] in
theorem map_star_starQuotEquivOfBot {M I : Subgroup G} (hker : kerIn (M ⊓ I) I = ⊥)
    (X : Subgroup G) :
    (star (M ⊓ I) I X).map (starQuotEquivOfBot hker).toMonoidHom = X.subgroupOf I := by
  rw [star, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (X.subgroupOf I)]
  congr 1

omit [Finite G] in
theorem not_isPGroup_two_of_simple {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) : ¬ IsPGroup 2 Y := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card Y = 2 := h2.isSimpleGroup_iff_card_eq.mp hs
  have : IsCyclic Y := isCyclic_of_prime_card hc
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (IsCyclic.commGroup.mul_comm a b)

theorem isInIHTVC_of_simple {H T M V I : Subgroup G} (hIH : I ≤ H) {h : G} (hhI : h ∈ I)
    (hI : I = V ⊔ conjSub h V) (hVTI : V ≤ T ⊓ I) (hV1 : V ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {k : ℕ} (hk : 1 < k) (hY : IsPSL 2 2 k ↥I ∨ IsSz k ↥I)
    (hMI : M ⊓ I = I ⊓ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G))
    (hn : ∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞)) : ASInputs.IsInIHTVC H T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup ↥I := isSimpleGroup_of_psl_or_sz hY
  have hnab := nonabelian_of_psl_or_sz hk hY
  have hTIn : ¬ I ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
    intro hle
    have hnorm : ((T ⊓ I).subgroupOf I).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hle
    rcases hs.eq_bot_or_eq_top_of_normal ((T ⊓ I).subgroupOf I) with h1 | h1
    · apply hV1
      rw [Subgroup.subgroupOf_eq_bot] at h1
      exact eq_bot_iff.mpr fun v hv =>
        (Subgroup.mem_bot).mpr ((Subgroup.disjoint_def.mp h1) (hVTI hv) (hVTI hv).2)
    · apply not_isPGroup_two_of_simple hs hnab
      have hIT : I ≤ T := fun x hx => by
        have : (⟨x, hx⟩ : ↥I) ∈ (T ⊓ I).subgroupOf I := by rw [h1]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      exact hsyl.2.1.to_le (le_inf hIT le_rfl)
  have hker : kerIn (M ⊓ I) I = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal ((kerIn (M ⊓ I) I).subgroupOf I) with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      have hle : kerIn (M ⊓ I) I ≤ I := kerIn_le.trans inf_le_right
      exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        ((Subgroup.disjoint_def.mp h1) hx (hle hx))
    · exfalso
      apply hTIn
      intro x hx
      have : (⟨x, hx⟩ : ↥I) ∈ (kerIn (M ⊓ I) I).subgroupOf I := by rw [h1]; trivial
      have hxM : x ∈ M ⊓ I := kerIn_le (Subgroup.mem_subgroupOf.mp this)
      rw [hMI] at hxM
      exact hxM.2
  have hS2 : IsPGroup 2 ↥((T ⊓ I).subgroupOf I) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  refine ⟨hIH, ⟨h, hhI, hI⟩, hsyl, ?_, k, hn, Or.inl ⟨hk, ?_, ?_⟩⟩
  · rw [hker]
    have hb : pCoreOf 2 (⊥ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)
    rw [hb]
    refine ⟨le_rfl, IsPGroup.of_bot, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  · rcases hY with hY | hY
    · exact Or.inl (isPSL_of_mulEquiv (starQuotEquivOfBot hker) hY)
    · exact Or.inr (isSz_of_mulEquiv' (starQuotEquivOfBot hker) hY)
  · refine isBorelIn_of_map_equiv (starQuotEquivOfBot hker) ?_
    rw [map_star_starQuotEquivOfBot hker (M ⊓ I), hMI, Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq inf_le_right]
    refine ⟨(T ⊓ I).subgroupOf I, ⟨le_top, hS2, ?_⟩, by rw [top_inf_eq]⟩
    change ¬ 2 ∣ ((T ⊓ I).subgroupOf I).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hsyl.2.2

omit [Finite G] in
theorem center_eq_bot_of_simple' {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center Y := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.mp hb a))

theorem centralizer_eq_bot_of_simple {Y : Type} [Group Y] [Finite Y] {T M K : Subgroup Y}
    (hmp : MinParabolic (⊤ : Subgroup Y) T M) (hJ : kerIn M ⊤ = ⊥) (hKn : K.Normal)
    (hs : IsSimpleGroup ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hKT : K ⊔ T = ⊤) :
    Subgroup.centralizer (K : Set Y) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set Y) with hC
  have hZ := center_eq_bot_of_simple' hs hnab
  have hCK : ∀ x, x ∈ C → x ∈ K → x = 1 := by
    intro x hxC hxK
    have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have hT2 : IsPGroup 2 (T.map (QuotientGroup.mk' K)) := hmp.isSylow.2.1.map _
  have hTtop : T.map (QuotientGroup.mk' K) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hy : y ∈ ((K ⊔ T : Subgroup Y) : Set Y) := by rw [hKT]; trivial
    rw [Subgroup.normal_mul] at hy
    obtain ⟨k, hk, t, ht, rfl⟩ := hy
    refine ⟨t, ht, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have := hKn.conj_mem _ hk t⁻¹
    simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 (Y ⧸ K) := by
    rw [hTtop] at hT2
    exact hT2.of_equiv Subgroup.topEquiv
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨j, hj⟩ := hQ2 (QuotientGroup.mk (c : Y))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
    exact ⟨j, Subtype.ext (hCK _ (C.pow_mem c.2 _) hj)⟩
  have hCn : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (C : Set Y) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx k hk
      have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
      have := hx _ hk'
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * k := by group
    · intro hx k hk
      have hk' : g * k * g⁻¹ ∈ K := hKn.conj_mem k hk g
      have := hx _ hk'
      calc k * x = g⁻¹ * ((g * k * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * k * g⁻¹)) * g := by rw [this]
        _ = x * k := by group
  have hle : C ≤ pCoreOf 2 (⊤ : Subgroup Y) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hCn hC2
  have h2 := hle.trans (hmp.pCoreOf_le_kerIn)
  rw [hJ] at h2
  exact le_bot_iff.mp h2

omit [Finite G] in
theorem exists_not_mem_normalizer_of_simple {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hs : IsSimpleGroup ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hSK : IsSylowTwoOf S K)
    (hS1 : S ≠ ⊥) : ∃ g ∈ K, g ∉ Subgroup.normalizer (S : Set Y) := by
  by_contra hall
  push Not at hall
  have hnorm : (S.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSK.1).mpr fun g hg => hall g hg
  rcases hs.eq_bot_or_eq_top_of_normal (S.subgroupOf K) with h1 | h1
  · apply hS1
    rw [Subgroup.subgroupOf_eq_bot] at h1
    exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
      ((Subgroup.disjoint_def.mp h1) hx (hSK.1 hx))
  · apply not_isPGroup_two_of_simple hs hnab
    have hKS : K ≤ S := fun x hx => by
      have : (⟨x, hx⟩ : ↥K) ∈ S.subgroupOf K := by rw [h1]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    exact hSK.2.1.to_le hKS

omit [Finite G] in
theorem nonabelian_of_perfect_of_surjective {A B : Type} [Group A] [Group B] [Group.IsPerfect A]
    [Nontrivial B] (f : A →* B) (hf : Function.Surjective f) : ∃ a b : B, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hker : commutator A ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hc (f a) (f b)]
    group
  rw [Group.IsPerfect.commutator_eq_top] at hker
  obtain ⟨x, y, hxy⟩ := exists_pair_ne B
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  apply hxy
  rw [hker (Subgroup.mem_top a), hker (Subgroup.mem_top b)]

theorem nParam_star_of_kerIn_eq_bot {M H : Subgroup G} (hJ : kerIn M H = ⊥) :
    E1.nParam (⊤ : Subgroup (StarQuot M H)) = E1.nParam H := by
  have := E2P.finite_starQuot M H
  let e : StarQuot M H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hJ, Subgroup.bot_subgroupOf])).trans
      QuotientGroup.quotientBot
  rw [E1.Eleven.nParam_top_mulEquiv e, ← E1.nParam_subgroupOf]

variable {H T M V : Subgroup G}

omit [Finite G] in
theorem card_star_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) {X : Subgroup G} (hXH : X ≤ H) :
    Nat.card ↥(star M H X) = Nat.card ↥X := by
  have hinj : Function.Injective (E2P.starMap M H) := by
    rw [← MonoidHom.ker_eq_bot_iff, E2P.ker_starMap, hJ, Subgroup.bot_subgroupOf]
  rw [star, ← E2P.starMap, Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]

theorem star_inf_eq_of_isBorelIn {K : Subgroup G} (h : MinParabolic H T M)
    (hKN : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer (star M H K : Set _))
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K))) :
    star M H M ⊓ star M H K = star M H K ⊓
      Subgroup.normalizer ((star M H T ⊓ star M H K : Subgroup (StarQuot M H)) : Set _) := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmpY := E2P.minParabolic_star h
  have hS : IsSylowTwoOf (star M H T ⊓ star M H K) (star M H K) :=
    A4.isSylowTwoOf_inf_normal hmpY.isSylow le_top hKN
  obtain ⟨S, hSsyl, hSeq⟩ := hB
  rw [E2P.star_inf_M] at hSeq
  have hTM : star M H T ⊓ star M H K ≤ star M H M ⊓ star M H K :=
    inf_le_inf_right _ (star_mono h.le)
  rw [hSeq] at hTM
  have hTS : star M H T ⊓ star M H K ≤ S := by
    have hsup : IsPGroup 2 ↥((star M H T ⊓ star M H K) ⊔ S) :=
      IsPGroup.to_sup_of_normal_right' hS.2.1 hSsyl.2.1 (hTM.trans inf_le_right)
    have hle : (star M H T ⊓ star M H K) ⊔ S ≤ star M H K := sup_le hS.1 hSsyl.1
    have := (A4.isSylowTwoOf_iff_maximal.mp hSsyl).2.2 _ hle hsup le_sup_right
    exact le_sup_left.trans this
  have hSeq' : S = star M H T ⊓ star M H K :=
    le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hS).2.2 S hSsyl.1 hSsyl.2.1 hTS) hTS
  rw [hSeq, hSeq']

theorem exists_isInIHTVC_of_bender (hKG1 : KGBenderInner) (hKG2L2 : KGBenderSubL2)
    (hKG2Sz : KGBenderSubSz) (hKG2U3 : KGBenderSubU3) (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hBen : IsBenderOf n ↥(star M H K)) (hB : IsBorelIn (star M H K) (star M H (M ⊓ K)))
    (hnstar : E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) (hSQs : SQTKGroup (StarQuot M H))
    (hV4 : 4 ≤ Nat.card V) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hY28 := h.star (sqtkGroup_top hSQs)
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY : kerIn (star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
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
  have hs : IsSimpleGroup ↥(star M H K) := by
    obtain ⟨-, hY | hY | hY⟩ := hBen
    · exact isSimpleGroup_of_psl_or_sz (Or.inl hY)
    · exact isSimpleGroup_of_psl_or_sz (Or.inr hY)
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hY).2
  have hnab : ∃ a b : ↥(star M H K), a * b ≠ b * a := by
    have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
    have : Nontrivial ↥(star M H K) := hs.toNontrivial
    exact nonabelian_of_perfect_of_surjective
      (((E2P.starMap M H).subgroupMap (K.subgroupOf H)).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (((E2P.starMap M H).subgroupMap_surjective _).comp
        (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hcent := centralizer_eq_bot_of_simple hmpY hJY hKn hs hnab hKT
  have hS : IsSylowTwoOf (star M H T ⊓ star M H K) (star M H K) :=
    A4.isSylowTwoOf_inf_normal hmpY.isSylow le_top hKN
  have hMK := star_inf_eq_of_isBorelIn h.minParabolic hKN hB
  obtain ⟨hO2K, hcentral⟩ := hKG1 (StarQuot M H) ⊤ (star M H T) (star M H M) (star M H K) n
    hmpY hJY le_top hKN (by rw [top_inf_eq]; exact hcent) hKT hBen hMK
  have hVK : star M H V ≤ star M H K := hY28.le_pCoreOf.trans hO2K
  have hVS : star M H V ≤ star M H T ⊓ star M H K := le_inf hY28.le_T hVK
  have hVZ : star M H V ≤
      Subgroup.centralizer ((star M H T ⊓ star M H K : Subgroup _) : Set (StarQuot M H)) :=
    fun x hx => hcentral x (hVS hx) (hY28.elem.2 x hx)
  have hV4s : 4 ≤ Nat.card ↥(star M H V) := by
    rw [card_star_of_kerIn_eq_bot hJ h.le_H]
    exact hV4
  obtain ⟨g₀, hg₀K, hg₀N⟩ := exists_not_mem_normalizer_of_simple hs hnab hS
    (fun hb => hY28.ne_bot (le_bot_iff.mp (hb ▸ hVS)))
  obtain ⟨g, hgK, hgN, hsyl, ⟨k, hk2, hkn, hYk⟩, hBor, ⟨h₀, hh₀, hI₀⟩⟩ :=
    exists_member_of_bender hBen hS hVS hV4s hg₀K hg₀N
      (kgBenderSub_b_of_parts hKG2L2 hKG2Sz hKG2U3 hBen hS hVS hVZ hY28.elem hV4s)
  set I₀ := star M H V ⊔ conjSub g (star M H V) with hI₀def
  have hI₀K : I₀ ≤ star M H K := sup_le hVK (by
    intro w hw
    rw [mem_conjSub] at hw
    have := (star M H K).mul_mem ((star M H K).mul_mem hgK (hVK hw)) ((star M H K).inv_mem hgK)
    simpa [mul_assoc] using this)
  have hTI : star M H T ⊓ I₀ = (star M H T ⊓ star M H K) ⊓ I₀ := by
    rw [inf_assoc, inf_eq_right.mpr hI₀K]
  have hmem : ASInputs.IsInIHTVC ⊤ (star M H T) (star M H M) (star M H V) I₀ := by
    refine isInIHTVC_of_simple le_top hh₀ hI₀ (le_inf hY28.le_T le_sup_left) hY28.ne_bot
      (by rw [hTI]; exact hsyl) (by omega) hYk ?_ ?_
    · rw [hTI, ← hBor, ← hMK, inf_assoc, inf_eq_right.mpr hI₀K]
    · obtain ⟨m, rfl⟩ := hkn
      exact ⟨m, by rw [hnstar]⟩
  exact exists_isInIHTVC_of_star h (nParam_star_of_kerIn_eq_bot hJ) hmem

theorem nParam_finite_of_e22 (hE22 : E22StatementC) (h : Hyp28 H T M V)
    (hns : ¬ Group.IsSolvable ↥H) : ∃ m : ℕ, E1.nParam H = m := by
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, hSQs⟩ := hE22.1 G H T M h.minParabolic h.sqtk hns
  have hNP := hE22.2 G H T M K h.minParabolic h.sqtk hns hKc hHK hq hcases hSQs
  have hfin : ∀ n : ℕ, E1.nParam H ≤ n → ∃ m : ℕ, E1.nParam H = m := fun n hn =>
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hn)).symm⟩
  dsimp only [E22CasesNoN] at hcases
  dsimp only [E22NParamCases] at hNP
  rcases hcases with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ, h2⟩
  · obtain ⟨hA, hB⟩ := hNP.1 hJ ⟨t, ht, hne, hM⟩
    rcases h1 with ⟨n, hn, hty, hBor⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    · exact hfin n (hA n hn hty hBor)
    · exact ⟨1, by rw [hB p hp hp8 hK hMK haut]; rfl⟩
  · obtain ⟨h2a, h2b, h2c, h2d⟩ := hNP.2 hTK hJ
    rcases h2 with ⟨n, hBen, hBor⟩ | ⟨n, hn, hty, hD, hBor⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    · exact hfin n (h2a n hBen hBor).1
    · exact hfin n (h2b n hn hty hD hBor).1
    · exact ⟨1, by rw [h2c p e hp hp3 he hpe hK hMK haut]; rfl⟩
    · exact ⟨1, by rw [h2d p hp hp2 hK hMK]; rfl⟩

theorem exists_isInIHTVC_of_card_two_e22 (hE22 : E22StatementC) (h : Hyp28 H T M V)
    (hJ : kerIn M H = ⊥) (hns : ¬ Group.IsSolvable ↥H) (hV : Nat.card V = 2) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I :=
  h.exists_isInIHTVC_of_card_two hJ hV (nParam_finite_of_e22 hE22 h hns)

end E2

end CFSG.Quasithin
