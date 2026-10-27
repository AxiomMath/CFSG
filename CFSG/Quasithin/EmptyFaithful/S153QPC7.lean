module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn5
public import CFSG.Quasithin.EmptyFaithful.S153QPC5
public import CFSG.Quasithin.EmptyFaithful.S153QPC6
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.Quasithin.EmptyFaithful.SBc17Inn4

public section

namespace CFSG.Quasithin.SBc17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.QP
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def actHom {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) :
    ↥J →* ↥(autOn J V) :=
  ((conjAct V).comp (Subgroup.inclusion hJV)).codRestrict (autOn J V)
    (fun j => mem_autOn_iff.mpr ⟨j, hJV j.2, j.2, rfl⟩)

theorem actHom_apply {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) (j : ↥J) :
    ((actHom hJV j : ↥(autOn J V)) : MulAut ↥V) = conjAct V ⟨(j : G), hJV j.2⟩ := rfl

theorem actHom_surjective {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actHom hJV) := by
  rintro ⟨s, hs⟩
  obtain ⟨x, hx, hxJ, rfl⟩ := mem_autOn_iff.mp hs
  exact ⟨⟨x, hxJ⟩, rfl⟩

theorem forall_isCyclic_of_pRank_le_one [Finite G] {J : Subgroup G} (h5 : pRank 5 J ≤ 1) :
    ∀ P : Subgroup ↥J, IsPGroup 5 P → IsCyclic P := by
  intro P hP
  have hr : CFSG.pRank 5 ↥J ≤ 1 := h5
  have hSL : P.map J.subtype ≤ J := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS : IsPGroup 5 ↥(P.map J.subtype) :=
    hP.of_equiv (P.equivMapOfInjective J.subtype J.subtype_injective)
  have hc := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one (p := 5) (by norm_num) (by norm_num)
    hSL hS hr
  exact isCyclic_of_surjective (P.equivMapOfInjective J.subtype J.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem actHom_ne_one_of_orderOf_five [Finite G] {J V : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J)
    (h5J : ∀ P : Subgroup ↥J, IsPGroup 5 P → IsCyclic P) {a : G} (haJ : a ∈ J)
    (ha5 : orderOf a = 5) : actHom hJV ⟨a, haJ⟩ ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hπa
  have ha'5 : (⟨a, haJ⟩ : ↥J) ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← ha5]
    exact pow_orderOf_eq_one a
  have hca : conjAct V ⟨a, hJV haJ⟩ = 1 := congrArg (fun s : ↥(autOn J V) => (s : MulAut ↥V)) hπa
  have haC : a ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := congrArg (fun m : MulAut ↥V => ((m ⟨v, hv⟩ : ↥V) : G)) hca
    simp only [conjAct_coe, MulAut.one_apply] at this
    calc v * a = (a * v * a⁻¹) * a := by rw [this]
      _ = a * v := by group
  have haZ : a ∈ oTwoZIn J := hD ⟨haJ, haC⟩
  obtain ⟨hxJ, hcen⟩ := mem_oTwoZIn_iff.1 haZ
  have : Group.IsPerfect (↥J ⧸ CFSG.pCore 2 ↥J) := hq.1
  have hcyc : ∀ E : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J), IsPGroup 5 E → IsCyclic E :=
    forall_isCyclic_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      (QuotientGroup.mk'_surjective _) h5J
  obtain ⟨P⟩ : Nonempty (Sylow 5 (↥J ⧸ CFSG.pCore 2 ↥J)) := inferInstance
  have hab : ∀ x ∈ (P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)), ∀ y ∈ (P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)),
      x * y = y * x := by
    have hc : IsCyclic (P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) := hcyc _ P.isPGroup'
    intro x hx y hy
    let _ := IsCyclic.commGroup (α := (P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)))
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : (P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))) ⟨y, hy⟩)
  have hz5 : (QuotientGroup.mk (⟨a, haJ⟩ : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, ha'5, QuotientGroup.mk_one]
  have hz1 := eq_one_of_mem_center_of_isPerfect P hab hcen hz5
  have hmem : (⟨a, haJ⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff _).1 hz1
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨⟨a, haJ⟩, hmem⟩
  have hpow : a ^ 2 ^ m = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥J) => ((z : ↥J) : G)) hm
    simpa using this
  have hdvd : orderOf a ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
  rw [ha5] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)

theorem false_of_c27SL3_inner [Finite G] {J V Mx K₁ : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J)
    (e : ↥(autOn J V) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hmax : IsMaxParabolic2 (autOn J V) (autOn (Mx ⊓ J) V)) (h5 : pRank 5 J ≤ 1)
    (hK₁M : K₁ ≤ Mx ⊓ J) (hK₁N : ∀ b ∈ Mx ⊓ J, ∀ k ∈ K₁, b * k * b⁻¹ ∈ K₁)
    {a : G} (haK : a ∈ K₁) (ha5 : orderOf a = 5)
    (hshape : IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ ∃ (O : Subgroup ↥K₁) (_ : O.Normal), IsPGroup 2 O ∧
      Nonempty (↥K₁ ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set π := actHom hJV with hπdef
  set φ : ↥J →* Matrix.SpecialLinearGroup (Fin 3) F := e.toMonoidHom.comp π with hφdef
  have hφs : Function.Surjective φ := e.surjective.comp (actHom_surjective hJV)
  have h5J := forall_isCyclic_of_pRank_le_one h5
  have h5S : ∀ E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), IsPGroup 5 E → IsCyclic E :=
    forall_isCyclic_of_surjective φ hφs h5J
  have hq5 : ¬ 5 ∣ Nat.card F - 1 := fun h => by
    obtain ⟨E, hE, hnc⟩ := exists_not_isCyclic_isPGroup_five h
    exact hnc (h5S E hE)
  have haJ : a ∈ J := (hK₁M haK).2
  set a' : ↥J := ⟨a, haJ⟩ with ha'
  have ha'5 : a' ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ha']
    rw [← ha5]
    exact pow_orderOf_eq_one a
  have hφa : φ a' ≠ 1 := fun h1 =>
    actHom_ne_one_of_orderOf_five hJV hq hD h5J haJ ha5 (e.injective (by simpa [hφdef] using h1))
  set K' : Subgroup ↥J := K₁.subgroupOf J with hK'
  have haK' : a' ∈ K' := haK
  set N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := K'.map φ with hN
  have hxN : φ a' ∈ N := ⟨a', haK', rfl⟩
  have hx5 : orderOf (φ a') = 5 := by
    refine orderOf_eq_prime ?_ hφa
    rw [← map_pow, ha'5, map_one]
  have hP := isMaxParabolic2_top_of_mulEquiv hmax e
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((autOn (Mx ⊓ J) V).subgroupOf (autOn J V)).map e.toMonoidHom with hPdef
  have hNP : N ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨π k, ?_, rfl⟩
    show ((π k : ↥(autOn J V)) : MulAut ↥V) ∈ autOn (Mx ⊓ J) V
    rw [hπdef, actHom_apply]
    exact mem_autOn_iff.2 ⟨k, hJV k.2, hK₁M hk, rfl⟩
  have hnorm : ∀ p ∈ P, ∀ y ∈ N, p * y * p⁻¹ ∈ N := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨k, hk, rfl⟩
    have hs' : (s : MulAut ↥V) ∈ autOn (Mx ⊓ J) V := hs
    obtain ⟨b, hbV, hb, hbs⟩ := mem_autOn_iff.mp hs'
    have hbJ : b ∈ J := hb.2
    have hsπ : s = π ⟨b, hbJ⟩ := Subtype.ext (by rw [hπdef, actHom_apply]; exact hbs.symm)
    refine ⟨⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹, ?_, ?_⟩
    · show ((⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹ : ↥J) : G) ∈ K₁
      simpa using hK₁N b hb k hk
    · rw [hsπ]
      simp [hφdef]
  have hshape' : IsPGroup 2 ↥⁅N, N⁆ ∨ 17 ∣ Nat.card N := by
    rcases hshape with h2 | ⟨O, hO, hO2, ⟨eO⟩⟩
    · left
      have hcomm : ⁅N, N⁆ = ⁅K', K'⁆.map φ := (Subgroup.map_commutator K' K' φ).symm
      have hcG : ⁅K', K'⁆.map J.subtype = ⁅K₁, K₁⁆ := by
        rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le (hK₁M.trans inf_le_right)]
      intro y
      have hy : (y : Matrix.SpecialLinearGroup (Fin 3) F) ∈ ⁅K', K'⁆.map φ := by
        rw [← hcomm]
        exact y.2
      obtain ⟨c, hc, hcy⟩ := hy
      have hcG' : ((c : ↥J) : G) ∈ ⁅K₁, K₁⁆ := hcG ▸ ⟨c, hc, rfl⟩
      obtain ⟨m, hm⟩ := h2 ⟨(c : G), hcG'⟩
      refine ⟨m, ?_⟩
      apply Subtype.ext
      have hcm : c ^ 2 ^ m = 1 := by
        have h1 : ((c : ↥J) : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
        apply Subtype.ext
        simpa using h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hcy, ← map_pow, hcm, map_one]
    · right
      have hK₁J : K₁ ≤ J := hK₁M.trans inf_le_right
      let π₁ : ↥K₁ →* ↥N := (φ.comp (Subgroup.inclusion hK₁J)).codRestrict N
        (fun k => ⟨Subgroup.inclusion hK₁J k, k.2, rfl⟩)
      have hπ₁ : Function.Surjective π₁ := by
        rintro ⟨_, k, hk, rfl⟩
        exact ⟨⟨(k : G), hk⟩, rfl⟩
      have hO' : IsPGroup 2 O := hO2
      rcases isPGroup_two_or_seventeen_dvd π₁ hπ₁ hO2 eO with h | h
      · exfalso
        obtain ⟨m, hm⟩ := h ⟨φ a', hxN⟩
        have hpow : (φ a') ^ 2 ^ m = 1 := congrArg Subtype.val hm
        have hdvd : orderOf (φ a') ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
        rw [hx5] at hdvd
        exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)
      · exact h
  exact hq5 (five_dvd_card_sub_one_of_normal_parabolic hP hNP hnorm hxN hx5 hshape')

theorem kOne_shape [Finite G] {T M H H₀ H₁ H₂ K₁ K₂ : Subgroup G} {p : ℕ} {t s : G}
    (hp5 : p = 5) (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ ∃ (O : Subgroup ↥K₁) (_ : O.Normal), IsPGroup 2 O ∧
      Nonempty (↥K₁ ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  rcases hset.shape with ⟨-, -, -, hφ⟩ | ⟨hK₁e, -⟩
  · right
    exact ⟨CFSG.Open.pCore 2 ↥K₁, CFSG.LieType.BorelTits.pCore_normal 2,
      CFSG.LieType.BorelTits.pCore_isPGroup 2, hφ⟩
  · left
    subst hK₁e
    have : NeZero p := ⟨by omega⟩
    have hle := commutator_oTwoUpper_le hdec
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hle

end CFSG.Quasithin.SBc17

namespace CFSG.Quasithin.SBc17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.QP CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

theorem input14615ContraInnerF_proved : Input14615ContraInnerF := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL hg
  have hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) := hHyp.radical.1.trans hJn
  obtain ⟨hJV, hD, -⟩ := inner_facts hC27 hHyp hJc hJq hchar hJle hR
  obtain ⟨⟨n, F, _, _, -, hcard, ⟨e⟩⟩, hmax', -⟩ := hg
  have : CharP F 2 := charP_two_of_card_eq_pow hcard
  have : Finite F := Finite.of_fintype F
  have e' : ↥(autOn J (omegaOneCenterOf (pCoreOf 2 (J ⊔ pCoreOf 2 (mcOf T))))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  obtain ⟨a, haO, ha5⟩ := hdec.exists_order_p_P14 hred.prime hred.odd
  have haK₁ : a ∈ K₁ := hset.oTwo₁ haO
  have ha5' : orderOf a = 5 := by rw [ha5, hctx.1]
  have hK₁M : K₁ ≤ g12_14615 T K₂ ⊓ J := fun x hx =>
    ⟨⟨sup_le_mcOf_14615 S hred hset (Subgroup.mem_sup_left hx),
      le_of_mem_cComp hJc (hK₁J hx)⟩, hK₁J hx⟩
  have hK₁N' : ∀ b ∈ g12_14615 T K₂ ⊓ J, ∀ k ∈ K₁, b * k * b⁻¹ ∈ K₁ := fun b hb k hk =>
    (Subgroup.mem_normalizer_iff.mp (hfix b hb.1.1 hb.1.2) k).mp hk
  exact false_of_c27SL3_inner hJV hJq hD e' hmax' hJ5 hK₁M hK₁N' haK₁ ha5'
    (kOne_shape hctx.1 hdec hset)

end CFSG.Quasithin.SBc17
