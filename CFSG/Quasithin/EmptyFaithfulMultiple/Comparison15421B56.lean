module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Glue
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace C421

theorem le_or_commute {X : Type*} [Group X] [Finite X] {K J N : Subgroup X}
    (hK : CFSG.IsComponent K) (hJ : J.Normal) (hNJ : N ≤ J)
    (hJN : ∀ a ∈ J, ∀ b ∈ N, a * b * a⁻¹ ∈ N) :
    K ≤ N ∨ ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := by
  have hNs : N.IsSubnormal := by
    refine Subgroup.IsSubnormal.step N J hNJ hJ.isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff hNJ]
    intro h k hh hk
    exact hJN k hk h hh
  rcases CFSG.LocalCores.component_subnormal_subgroup hK hNs with h | h
  · exact Or.inl h
  · right
    intro k hk n hn
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk
    exact (Subgroup.mem_centralizer_iff.mp this n hn).symm

variable {G : Type} [Group G] [Finite G]

section Setting

variable {I V G₁ G₂ : Subgroup G} (hV : IsElemAbelian 2 V)
  (hIV : I ≤ Subgroup.normalizer (V : Set G))
  (hC : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)

include hIV hC in
theorem pCoreOf_autI_eq_bot : pCoreOf 2 (autI hV I) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices h : Open.pCore 2 ↥(autI hV I) = ⊥ by
    change (Open.pCore 2 ↥(autI hV I)).map (autI hV I).subtype = ⊥
    rw [h, Subgroup.map_bot]
  set Q := (Open.pCore 2 ↥(autI hV I)).comap (conjI hV hIV) with hQdef
  have hQn : Q.Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap _
  have hQ2 : IsPGroup 2 ↥Q := by
    rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(autI hV I)) 2)
      ⟨conjI hV hIV k, hk⟩
    have h1 : k ^ 2 ^ n ∈ Open.pCore 2 ↥I := by
      rw [← conjI_eq_one_iff_mem hV hIV hC, map_pow]
      exact congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥I) 2) ⟨_, h1⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hQP : Q ≤ Open.pCore 2 ↥I := CFSG.LieType.BorelTits.le_pCore 2 hQn hQ2
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := conjI_surjective hV hIV x
  exact (Subgroup.mem_bot).mpr ((conjI_eq_one_iff_mem hV hIV hC k).mpr (hQP hx))

include hIV in
theorem isQuotientOfSQTKCat_autI (hI : CFSG.SectionRank.IsSQTKCat ↥I) :
    G64.IsQuotientOfSQTKCat ↥(autI hV I) :=
  ⟨↥I, inferInstance, inferInstance, (conjI hV hIV).ker, inferInstance, hI,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (conjI_surjective hV hIV)).symm⟩⟩

include hIV hC in
theorem b53Hyp_ffJ (hI : CFSG.SectionRank.IsSQTKCat ↥I) : B53Hyp (ffJ (autI hV I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX := FFL.ffJ_le (autI hV I)
  refine ⟨?_, (FFL.ffJ_ffJ _).symm, ?_⟩
  · rw [eq_bot_iff, ← pCoreOf_autI_eq_bot hV hIV hC]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hJX)
      ((FFL.le_normalizer_ffJ (autI hV I)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ :=
      G64.isQuotientOfSQTKCat_of_le hJX (isQuotientOfSQTKCat_autI hV hIV hI)
    exact ⟨Y, inferInstance, inferInstance, N, inferInstance, G64.sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

end Setting

theorem two_dvd_card_statedSL_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [FFL.card_statedSL_two]
  exact Dvd.dvd.mul_right ((CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)) _

theorem two_dvd_card_statedSL_three (K : Type) [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [FFL.card_statedSL_three]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow ?_ (by norm_num)) _) _
  exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)

theorem two_dvd_card_of_factorList {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : B56FactorList ↥H) : 2 ∣ Nat.card ↥H := by
  rcases h with ⟨n, K, _, _, -, hK, ⟨e⟩⟩ | he | ⟨m, K, _, _, -, -, hK, ⟨e⟩⟩
  · have := FFL.charP_two_of_card hK
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_statedSL_two K
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · have := FFL.charP_two_of_card hK
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_statedSL_three K

omit [Finite G] in
theorem le_or_commute_subgroupOf {Y : Type} [Group Y] [Finite Y] {X J N : Subgroup Y}
    {K : Subgroup ↥X} (hK : CFSG.IsComponent K)
    (hXJ : X ≤ Subgroup.normalizer (J : Set Y)) (hNJ : N ≤ J)
    (hJN : J ≤ Subgroup.normalizer (N : Set Y)) :
    K ≤ N.subgroupOf X ∨ ∀ k ∈ K, ∀ n ∈ N.subgroupOf X, k * n = n * k := by
  have hJn : (J.subgroupOf X).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXJ g.2) n).mp hn
  refine le_or_commute hK hJn (fun x hx => hNJ hx) ?_
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf] at ha hb ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hJN ha) b).mp hb

section Main

variable {I V G₁ G₂ : Subgroup G} (hV : IsElemAbelian 2 V)
  (hIV : I ≤ Subgroup.normalizer (V : Set G))
  (hC : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)
  (hI : CFSG.SectionRank.IsSQTKCat ↥I) (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
  (ham : IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
    ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))))
  (hF618 : F6.TheoremF618Cat) (hA : F618ComponentInspection)

include hIV hC hI ham hF618 hA htr in
theorem false_of_commute_even {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K)
    {H : Subgroup ↥(autI hV I)} (h2 : 2 ∣ Nat.card ↥H)
    (hcomm : ∀ k ∈ K, ∀ h ∈ H, k * h = h * k) : False := by
  obtain ⟨x, hx2, hx1⟩ := exists_sq_eq_one h2
  refine false_of_commute_sq hV hIV hC hI htr ham hF618 hA hK (x := (x : ↥(autI hV I))) ?_ ?_
    (fun k hk => hcomm k hk x x.2)
  · rw [← Subgroup.coe_pow, hx2, Subgroup.coe_one]
  · exact fun h0 => hx1 (Subtype.ext h0)

theorem card_subgroupOf {Y : Type} [Group Y] {X H : Subgroup Y} (hHX : H ≤ X) :
    Nat.card ↥(H.subgroupOf X) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv

include hIV hC hI ham hF618 hA htr in
theorem le_ffJ_of_isComponent (hFF : IsFFModule (autI hV I)) {K : Subgroup ↥(autI hV I)}
    (hK : CFSG.IsComponent K) : K ≤ (ffJ (autI hV I)).subgroupOf (autI hV I) := by
  have hJn : ((ffJ (autI hV I)).subgroupOf (autI hV I)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (FFL.le_normalizer_ffJ (autI hV I) g.2) n).mp hn
  rcases CFSG.LocalCores.component_normal_subgroup hK hJn with h | h
  · exact h
  · exfalso
    obtain ⟨A, hAoff⟩ := B6.exists_isFFStarOffender hFF
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAoff.2.1
    have ha2 : (a : MulAut (IntMod V hV)) ^ 2 = 1 := hAoff.2.2.1.2 a a.2
    have haJ : (a : MulAut (IntMod V hV)) ∈ ffJ (autI hV I) := B19.le_ffJ hAoff a.2
    set x : ↥(autI hV I) := ⟨a, hAoff.1 a.2⟩
    refine false_of_commute_sq hV hIV hC hI htr ham hF618 hA hK (x := x) (Subtype.ext ha2)
      (fun h0 => ha1 (Subtype.ext (by
        have h1 := congrArg Subtype.val h0
        exact h1))) fun k hk => ?_
    have hxJ : x ∈ (ffJ (autI hV I)).subgroupOf (autI hV I) := haJ
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk
    exact (Subgroup.mem_centralizer_iff.mp this x hxJ).symm

include hIV hC hI ham hF618 hA htr in
theorem b51Part1_of_isComponent (h56 : AsB56) (hFF : IsFFModule (autI hV I))
    {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K) :
    CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hV I))) ∧
      B51Part1 (ffJ (autI hV I)) (quasithinGenFitting (ffJ (autI hV I))) := by
  have hJX : (ffJ (autI hV I)) ≤ (autI hV I) := FFL.ffJ_le (autI hV I)
  have hXJ : (autI hV I) ≤ Subgroup.normalizer ((ffJ (autI hV I)) : Set (MulAut (IntMod V hV))) :=
    FFL.le_normalizer_ffJ (autI hV I)
  have hKJ := le_ffJ_of_isComponent hV hIV hC hI htr ham hF618 hA hFF hK
  have hB53 := b53Hyp_ffJ hV hIV hC hI
  have hJ1 : (ffJ (autI hV I)) ≠ ⊥ := by
    obtain ⟨A, hAoff⟩ := B6.exists_isFFStarOffender hFF
    intro h
    exact hAoff.2.1 (le_bot_iff.mp (h ▸ B19.le_ffJ hAoff))
  have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := IntMod.sq_eq_one
  have hKne : (K : Subgroup ↥(autI hV I)) ≠ ⊥ := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this
  have hpair : ∀ J₁ J₂ : Subgroup (MulAut (IntMod V hV)), J₁ ⊔ J₂ = (ffJ (autI hV I)) →
      (∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) → 2 ∣ Nat.card ↥J₁ → 2 ∣ Nat.card ↥J₂ → False := by
    intro J₁ J₂ hsup hcomm h₁ h₂
    have hcomm' : ∀ a ∈ J₂, ∀ b ∈ J₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
    have hJ₁J : J₁ ≤ (ffJ (autI hV I)) := hsup ▸ le_sup_left
    have hJ₂J : J₂ ≤ (ffJ (autI hV I)) := hsup ▸ le_sup_right
    have hN₁ : (ffJ (autI hV I)) ≤ Subgroup.normalizer (J₁ : Set (MulAut (IntMod V hV))) :=
      hsup.symm.le.trans (FFL.sup_le_normalizer hcomm)
    rcases le_or_commute_subgroupOf hK hXJ hJ₁J hN₁ with hle | hc
    · refine false_of_commute_even hV hIV hC hI htr ham hF618 hA hK
        (H := J₂.subgroupOf (autI hV I)) (by rwa [card_subgroupOf (hJ₂J.trans hJX)]) ?_
      intro k hk h hh
      exact Subtype.ext (hcomm _ (hle hk) _ hh)
    · exact false_of_commute_even hV hIV hC hI htr ham hF618 hA hK
        (H := J₁.subgroupOf (autI hV I)) (by rwa [card_subgroupOf (hJ₁J.trans hJX)]) hc
  rcases h56 (IntMod V hV) hV2 (ffJ (autI hV I)) hJ1 hB53 with ⟨hqF, ⟨h1, -⟩, -⟩ | h2 | h3 | h4 | h5
  · exact ⟨hqF, h1⟩
  ·
    exfalso
    obtain ⟨⟨e⟩, -, -⟩ := h2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    have hJs : Group.IsSolvable ↥(ffJ (autI hV I)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    let f : ↥K →* ↥(ffJ (autI hV I)) :=
      (((autI hV I).subtype.comp K.subtype).codRestrict (ffJ (autI hV I)) fun k => hKJ k.2)
    have hf : Function.Injective f := fun a b hab => by
      have := congrArg (fun y : ↥(ffJ (autI hV I)) => (y : MulAut (IntMod V hV))) hab
      exact Subtype.ext (Subtype.ext this)
    have hKs : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective hf
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have : Group.IsPerfect ↥K := hK.1.1
    exact Group.IsPerfect.not_isSolvable ↥K hKs
  ·
    exfalso
    obtain ⟨J₁, J₂, hsup, -, hcomm, h₁, h₂, -⟩ := h3
    exact hpair J₁ J₂ hsup hcomm (two_dvd_card_of_factorList h₁) (two_dvd_card_of_factorList h₂)
  ·
    exfalso
    obtain ⟨J₁, J₂, t, hG, -, hcomm, ⟨e₁⟩, hc3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
    have hcomm' : ∀ a ∈ J₂, ∀ b ∈ J₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
    have hJ₁J : J₁ ≤ (ffJ (autI hV I)) := hG ▸ le_sup_left.trans le_sup_left
    have hJ₂J : J₂ ≤ (ffJ (autI hV I)) := hG ▸ le_sup_right.trans le_sup_left
    have hN₁ : (ffJ (autI hV I)) ≤ Subgroup.normalizer (J₁ : Set (MulAut (IntMod V hV))) := by
      rw [hG]
      refine sup_le (FFL.sup_le_normalizer hcomm) ?_
      rw [Subgroup.zpowers_le]
      exact ht₁
    have hN₂ : (ffJ (autI hV I)) ≤ Subgroup.normalizer (J₂ : Set (MulAut (IntMod V hV))) := by
      rw [hG]
      refine sup_le ((sup_comm J₁ J₂).le.trans (FFL.sup_le_normalizer hcomm')) ?_
      rw [Subgroup.zpowers_le]
      exact ht₂
    have hK₂ : ∀ k ∈ K, ∀ n ∈ J₂.subgroupOf (autI hV I), k * n = n * k := by
      rcases le_or_commute_subgroupOf hK hXJ hJ₂J hN₂ with hle | hc
      · exfalso
        have h3 : Nat.card ↥K ∣ 3 := by
          rw [← hc3, ← card_subgroupOf (hJ₂J.trans hJX)]
          exact Subgroup.card_dvd_of_le hle
        have h2 := two_dvd_card_of_isQuasisimple hK.1
        have := Nat.dvd_trans h2 h3
        omega
      · exact hc
    have hc6 : Nat.card ↥J₁ = 360 := by
      rw [Nat.card_congr e₁.toEquiv, FFL.card_alt (by norm_num)]
      decide
    rcases le_or_commute_subgroupOf hK hXJ hJ₁J hN₁ with hle | hc
    ·
      set J₁' := J₁.subgroupOf (autI hV I) with hJ₁'
      have e₁' : ↥J₁' ≃* ↥(alternatingGroup (Fin 6)) :=
        (Subgroup.subgroupOfEquivOfLe (hJ₁J.trans hJX)).trans e₁
      have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      have hs : IsSimpleGroup ↥J₁' := e₁'.isSimpleGroup
      have hsub : (K.subgroupOf J₁').IsSubnormal := hK.2.subgroupOf
      have hKtop : K.subgroupOf J₁' = ⊤ := by
        rcases hsub.eq_bot_or_top_of_isSimpleGroup hs with h | h
        · exfalso
          apply hKne
          rw [eq_bot_iff]
          intro k hk
          have : (⟨k, hle hk⟩ : ↥J₁') ∈ K.subgroupOf J₁' := hk
          rw [h, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
        · exact h
      have hKeq : K = J₁' := by
        refine le_antisymm hle fun k hk => ?_
        have : (⟨k, hk⟩ : ↥J₁') ∈ K.subgroupOf J₁' := hKtop ▸ Subgroup.mem_top _
        exact this
      have eK : ↥K ≃* ↥(alternatingGroup (Fin 6)) := (MulEquiv.subgroupCongr hKeq).trans e₁'
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J₂.subgroupOf (autI hV I))) 3
        (by rw [card_subgroupOf (hJ₂J.trans hJX), hc3])
      refine false_of_commute_cube hV hIV hC hI htr ham hF618 hA hK eK (y := (y : ↥(autI hV I)))
        ?_ ?_ (fun k hk => hK₂ k hk y y.2)
      · rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
      · intro h0
        have : y = 1 := Subtype.ext h0
        rw [this, orderOf_one] at hy
        omega
    · exact false_of_commute_even hV hIV hC hI htr ham hF618 hA hK
        (H := J₁.subgroupOf (autI hV I)) (by rw [card_subgroupOf (hJ₁J.trans hJX), hc6]; decide) hc
  ·
    exfalso
    obtain ⟨J₁, J₂, hsup, -, hcomm, -, ⟨e₁⟩, -, -, h₂⟩ := h5
    have h₁ : 2 ∣ Nat.card ↥J₁ := by
      rw [Nat.card_congr e₁.toEquiv]
      exact two_dvd_card_statedSL_three (ZMod 2)
    have h₂' : 2 ∣ Nat.card ↥J₂ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hπ⟩
      · rw [Nat.card_congr e₂.toEquiv]
        exact two_dvd_card_statedSL_three (ZMod 2)
      · have := FFL.charP_two_of_card hF
        have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
        rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv]
        exact two_dvd_card_statedSL_two F
    exact hpair J₁ J₂ hsup hcomm h₁ h₂'

end Main

end C421

end CFSG.Quasithin.EmptyFaithfulMultiple
