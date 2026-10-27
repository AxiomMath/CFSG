module

public import CFSG.RankThree.PartOne.K133.Moving
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartOne.K133.KleinSL2

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

@[expose] def ResConfig (p : ℕ) (X : Type) [Group X] (Ē : Subgroup (MulAut X)) : Prop :=
  ∃ C : Subgroup (MulAut X), C ≤ Ē ∧ Nat.card C = p ^ 2 ∧ ∃ Kb : Subgroup X,
    IsSimpleGroup ↥Kb ∧ (∃ a b : Kb, a * b ≠ b * a) ∧ p ∣ Nat.card Kb ∧
      ∀ φ ∈ C, ∀ k ∈ Kb, φ k = k

@[expose] def GoodRes (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē → Nat.card Ē = p ^ 3 → ResConfig p X Ē →
    GoodAction p X Ē

theorem Good.goodRes {p : ℕ} {X : Type} [Group X] (h : Good p X) : GoodRes p X :=
  fun Ē hE hc _ => h Ē hE hc

@[expose] def ResConfigV (p : ℕ) (X : Type) [Group X] (Ē : Subgroup (MulAut X)) : Prop :=
  ∃ C : Subgroup (MulAut X), C ≤ Ē ∧ Nat.card C = p ^ 2 ∧ ∃ Kb : Subgroup X,
    IsSimpleGroup ↥Kb ∧ (∃ a b : Kb, a * b ≠ b * a) ∧ p ∣ Nat.card Kb ∧
      (∃ V : Subgroup X, V ≤ Kb ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
        ∀ φ ∈ C, ∀ k ∈ Kb, φ k = k

@[expose] def GoodResV (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē → Nat.card Ē = p ^ 3 → ResConfigV p X Ē →
    GoodAction p X Ē

theorem ResConfigV.toResConfig {p : ℕ} {X : Type} [Group X] {Ē : Subgroup (MulAut X)}
    (h : ResConfigV p X Ē) : ResConfig p X Ē := by
  obtain ⟨C, hCĒ, hCc, Kb, hKs, hKn, hpK, -, hfix⟩ := h
  exact ⟨C, hCĒ, hCc, Kb, hKs, hKn, hpK, hfix⟩

theorem GoodRes.toGoodResV {p : ℕ} {X : Type} [Group X] (h : GoodRes p X) : GoodResV p X :=
  fun Ē hE hc hR => h Ē hE hc hR.toResConfig

theorem simple_image {M N : Type*} [Group M] [Group N] (K : Subgroup M) (hK : IsSimpleGroup K)
    (hne : ∃ a b : K, a * b ≠ b * a) (φ : M →* N) (hφ : Group.IsSolvable φ.ker) :
    IsSimpleGroup ↥(K.map φ) ∧ (∃ a b : ↥(K.map φ), a * b ≠ b * a) ∧
      Nat.card ↥(K.map φ) = Nat.card K ∧ Function.Injective (φ.subgroupMap K) := by
  have hinj : Function.Injective (φ.subgroupMap K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hker : (φ.subgroupMap K).ker = ⊥ ∨ (φ.subgroupMap K).ker = ⊤ :=
      IsSimpleGroup.eq_bot_or_eq_top_of_normal _
    rcases hker with h | h
    · have : x ∈ (φ.subgroupMap K).ker := hx
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hne
      have hKle : K ≤ φ.ker := by
        intro k hk
        have : (⟨k, hk⟩ : K) ∈ (φ.subgroupMap K).ker := h ▸ Subgroup.mem_top _
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 this)
        exact MonoidHom.mem_ker.2 this
      have hsolK : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle)
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolK a b)
  let e : K ≃* ↥(K.map φ) := MulEquiv.ofBijective (φ.subgroupMap K) ⟨hinj, φ.subgroupMap_surjective K⟩
  refine ⟨e.symm.isSimpleGroup, ?_, (Nat.card_congr e.toEquiv).symm, hinj⟩
  obtain ⟨a, b, hab⟩ := hne
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem simpleQuotAction_apply {G : Type} [Group G] [Finite G] (p : ℕ) {E J : Subgroup G}
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) (x : ↥E) (y : ↥J) :
    simpleQuotAction p hEJ x
        ((((y : ↥J) : ↥J ⧸ aschbacherSolvableCore p ↥J)) : SimpleQuot p J) =
      (((J.normalizerMonoidHom ⟨(x : G), hEJ x.2⟩ y : ↥J) : ↥J ⧸ aschbacherSolvableCore p ↥J) :
        SimpleQuot p J) := rfl

theorem KF133ResMaxAt.of_goodResV (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r)
    {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      P X → ∀ p : ℕ, p.Prime → 5 ≤ p → GoodResV p X) :
    KF133ResMaxAt P := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hPJ
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEJ, hEl, hcard3⟩ := simpleQuotAction_image h hF hEA hb hb1 hJ hD
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ
  have hSimpleT : IsSimpleGroup (SimpleQuot p J) := hq.2.1
  obtain ⟨-, r, hr1, hr12, hrow, -, hrA, hr9⟩ := hF.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hrA (by omega))
  obtain ⟨f, hRMf, hKR, -⟩ :=
    hTypes r hr9' hr12 G p A c L E h hF hF13 hT hrow hrA hr9 t ht htL K hK
  have hmod : StatedClassicalModel ↥K .PSL 2 2 f := by
    interval_cases r <;> exact hKR
  have hpf : p ∣ 2 ^ f + 1 := by
    interval_cases r <;> simp only [RowModelF] at hRMf
    · exact hRMf.2.1
    · exact hRMf.2.1
    · rw [hRMf.1]; exact hRMf.2.2.2.1
    · rw [hRMf.1]; exact hRMf.2.2.2.1
  obtain ⟨hf2, F2, hF2, hFin2, hchar2, hcardF2, ⟨eK2⟩⟩ := S15K.exists_mulEquiv_sl2_of_model hmod
  obtain ⟨V₀, hV₀el, hV₀c⟩ := exists_klein_four_sl2 (F := F2) hf2 hcardF2
  have hKq := S15K.isQuasisimple_of_model hmod
  have hKc := S15K.center_eq_bot_of_model hmod
  let eKc : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
    ((QuotientGroup.quotientMulEquivOfEq hKc).trans QuotientGroup.quotientBot).symm
  have hKsimple : IsSimpleGroup ↥K := by
    have := hKq.2.1
    exact eKc.isSimpleGroup
  have hKnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hpK : p ∣ Nat.card ↥K := by
    obtain ⟨-, F, hF', hFin, hchar, hcardF, ⟨eK⟩⟩ := S15K.exists_mulEquiv_sl2_of_model hmod
    rw [Nat.card_congr eK.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hcardF]
    refine hpf.trans (Dvd.dvd.mul_left ?_ _)
    have : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      zify [h1, Nat.one_le_pow 2 (2 ^ f) (by omega)]
      ring
    rw [this]
    exact Dvd.intro _ rfl
  set θ' := aschbacherSolvableCore p ↥J with hθ'
  set π₁ : ↥J →* (↥J ⧸ θ') := QuotientGroup.mk' θ' with hπ₁
  set π₂ : (↥J ⧸ θ') →* SimpleQuot p J :=
    QuotientGroup.mk' (Subgroup.center (↥J ⧸ θ')) with hπ₂
  let Kj : Subgroup ↥J := K.subgroupOf J
  let eKj : Kj ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKJ
  have hKjs : IsSimpleGroup ↥Kj := eKj.isSimpleGroup
  have hKjn : ∃ a b : ↥Kj, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnonab
    exact ⟨eKj.symm a, eKj.symm b, fun h => hab (eKj.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hθsol : Group.IsSolvable π₁.ker := by
    rw [hπ₁, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization (H := ↥J) hp).1
  obtain ⟨hK1s, hK1n, hK1c, hK1i⟩ := simple_image Kj hKjs hKjn π₁ hθsol
  have hZsol : Group.IsSolvable π₂.ker := by
    rw [hπ₂, QuotientGroup.ker_mk']
    infer_instance
  obtain ⟨hK2s, hK2n, hK2c, hK2i⟩ := simple_image (Kj.map π₁) hK1s hK1n π₂ hZsol
  set Kb : Subgroup (SimpleQuot p J) := (Kj.map π₁).map π₂ with hKb
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F2 →* SimpleQuot p J :=
    Kb.subtype.comp ((π₂.subgroupMap (Kj.map π₁)).comp ((π₁.subgroupMap Kj).comp
      (eKj.symm.toMonoidHom.comp eK2.symm.toMonoidHom)))
  have hψinj : Function.Injective ψ :=
    Kb.subtype_injective.comp (hK2i.comp (hK1i.comp (eKj.symm.injective.comp eK2.symm.injective)))
  set f := simpleQuotAction p hEJ with hf
  set C₀ : Subgroup ↥E := autFixed E t with hC₀
  have hC₀G : autFixedInG E t = C₀.map E.subtype := rfl
  have hCcard : Nat.card ↥(autFixedInG E t) = p ^ 3 :=
    card_autFixedInG hp h.E_elem (card_E_of_ne hF hEA) (hF13.reflection t ht)
  have hC₀card : Nat.card C₀ = p ^ 3 := by
    rw [hC₀G, Subgroup.card_map_of_injective E.subtype_injective] at hCcard
    exact hCcard
  have hkerc : Nat.card f.ker = p := by
    have hmul := Subgroup.card_ker_mul_card_range f
    rw [card_E_of_ne hF hEA, hcard3] at hmul
    have hp0 : 0 < p ^ 3 := pow_pos hp.pos 3
    apply Nat.eq_of_mul_eq_mul_right hp0
    rw [hmul]
    ring
  have hbC : b ∈ autFixedInG E t := hb
  have hkerle : f.ker ≤ C₀ := by
    intro x hx
    have hxG : (x : G) ∈ thetaQuotientCentralizer p E J := by
      rw [thetaQuotientCentralizer_eq_map_ker p hEJ]
      exact ⟨x, (ker_simpleQuotAction p hq.1 hEJ x).1 hx, rfl⟩
    rw [hD] at hxG
    have hxC : (x : G) ∈ autFixedInG E t := Subgroup.zpowers_le.2 hbC hxG
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxC
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hCcard' : Nat.card (C₀.map f) = p ^ 2 := by
    set g : ↥C₀ →* MulAut (SimpleQuot p J) := f.comp C₀.subtype with hg
    have hmul := Subgroup.card_ker_mul_card_range g
    have hker2 : Nat.card g.ker = p := by
      have hkg : g.ker = f.ker.subgroupOf C₀ := by
        ext x
        simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rw [hkg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv]
      exact hkerc
    have hrg : g.range = C₀.map f := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hker2, hC₀card, hrg] at hmul
    have hp0 : 0 < p := hp.pos
    apply Nat.eq_of_mul_eq_mul_left hp0
    rw [hmul]
    ring
  have hRes : ResConfigV p (SimpleQuot p J) (simpleQuotAction p hEJ).range := by
    refine ⟨C₀.map f, Subgroup.map_le_range _ _, hCcard', Kb, hK2s, hK2n, ?_,
      ⟨V₀.map ψ, ?_, ?_, ?_⟩, ?_⟩
    · rw [hKb, hK2c, hK1c, Nat.card_congr eKj.toEquiv]
      exact hpK
    · rintro _ ⟨x, -, rfl⟩
      exact SetLike.coe_mem _
    · have := hV₀el
      exact IsElementaryAbelian.map ψ
    · rw [Subgroup.card_map_of_injective hψinj]
      exact hV₀c
    · rintro φ ⟨x, hx, rfl⟩ k hk
      obtain ⟨q, hqK, rfl⟩ := Subgroup.mem_map.1 hk
      obtain ⟨y, hyK, rfl⟩ := Subgroup.mem_map.1 hqK
      have hxC : (x : G) ∈ autFixedInG E t := ⟨x, hx, rfl⟩
      have hxK : (x : G) ∈ Subgroup.centralizer (K : Set G) :=
        autFixedInG_le_centralizer_of_isKt hK hxC
      have hyK' : (y : G) ∈ K := hyK
      have hcomm : (y : G) * (x : G) = (x : G) * (y : G) := Subgroup.mem_centralizer_iff.1 hxK _ hyK'
      have hfix : J.normalizerMonoidHom ⟨(x : G), hEJ x.2⟩ y = y := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        show (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
        rw [← hcomm]
        group
      have := simpleQuotAction_apply p hEJ x y
      rw [hfix] at this
      exact this
  exact exists_B_of_goodAction h hF hEA hb hb1 hJ hD hEJ hcard3
    (hP _ hq.2.2 hPJ p hp h5 _ hEl hcard3 hRes)

theorem KF133ResMaxAt.of_goodRes (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r)
    {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      P X → ∀ p : ℕ, p.Prime → 5 ≤ p → GoodRes p X) :
    KF133ResMaxAt P :=
  KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => (hP X hne hX p hp h5).toGoodResV

end CFSG.RankThree.PartOne.K133
